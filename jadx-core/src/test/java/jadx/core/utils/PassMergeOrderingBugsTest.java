package jadx.core.utils;

import java.util.ArrayList;
import java.util.List;

import org.junit.jupiter.api.Test;

import jadx.api.JadxArgs;
import jadx.api.impl.passes.DecompilePassWrapper;
import jadx.api.plugins.pass.JadxPass;
import jadx.api.plugins.pass.JadxPassInfo;
import jadx.api.plugins.pass.impl.OrderedJadxPassInfo;
import jadx.api.plugins.pass.types.JadxDecompilePass;
import jadx.core.Jadx;
import jadx.core.dex.nodes.ClassNode;
import jadx.core.dex.nodes.MethodNode;
import jadx.core.dex.nodes.RootNode;
import jadx.core.dex.visitors.AbstractVisitor;
import jadx.core.dex.visitors.IDexTreeVisitor;

import static jadx.tests.api.utils.assertj.JadxAssertions.assertThat;
import static java.util.Arrays.asList;
import static java.util.Collections.emptyList;
import static java.util.Collections.singletonList;

/**
 * Reproductions of plugin pass ordering bugs in {@link PassMerge} (present in jadx 1.5.6).
 * <p>
 * Every test registers plugin passes whose runAfter/runBefore constraints can be satisfied and
 * checks only what any correct merge has to do: succeed, keep built-in passes in their order, and
 * honour every declared constraint (START passes before and END passes after all built-in passes).
 * On the current implementation each test fails:
 * <ul>
 * <li>{@link #manyInterdependentPasses()}: IllegalArgumentException "Comparison method violates its
 * general contract!" (custom passes are sorted with a Comparator that is not a total order);</li>
 * <li>{@link #threePassesInRealPipeline()}, {@link #threePasses()},
 * {@link #smallSatisfiableSetups()}: JadxRuntimeException "Conflict order requirements" (passes are
 * inserted one at a time, and an early insertion can make a later constraint impossible);</li>
 * <li>{@link #startPassReferencedByAnotherPass()}, {@link #endPassReferencedByAnotherPass()}:
 * JadxRuntimeException "Ordering pass not found: start/end" (START/END are detected on dependency
 * lists that already contain names of other passes).</li>
 * </ul>
 */
class PassMergeOrderingBugsTest {

	/**
	 * 57 passes with dense but acyclic constraints, half of them anchored to built-in passes of the
	 * real pipeline.
	 */
	@Test
	void manyInterdependentPasses() {
		List<String> builtIns = realPipeline();
		String[] anchors = { "RegionMakerVisitor", "ModVisitor", "CodeShrinkVisitor", "EnumVisitor", "ClassModifier" };
		List<OrderedJadxPassInfo> passes = new ArrayList<>();
		for (int i = 0; i < 57; i++) {
			OrderedJadxPassInfo info = info("P" + i);
			if (i % 2 == 0) {
				info.after(anchors[i % anchors.length]);
			}
			for (int j = 0; j < i; j++) {
				if ((i * 7 + j * 13) % 3 == 0) {
					info.after("P" + j);
				}
			}
			for (int k = i + 1; k < 57; k++) {
				if ((i * 5 + k * 11) % 4 == 0) {
					info.before("P" + k);
				}
			}
			passes.add(info);
		}
		assertValidMerge(builtIns, passes);
	}

	/**
	 * Valid order: ..., RegionMakerVisitor, X, Y, Z, ...
	 */
	@Test
	void threePassesInRealPipeline() {
		assertValidMerge(realPipeline(), asList(
				info("X").before("Y"),
				info("Y"),
				info("Z").after("RegionMakerVisitor").after("Y")));
	}

	/**
	 * Same as {@link #threePassesInRealPipeline()} with a minimal pipeline. Valid order: a, X, Y, Z, b.
	 */
	@Test
	void threePasses() {
		assertValidMerge(asList("a", "b"), asList(
				info("X").before("Y"),
				info("Y"),
				info("Z").after("a").after("Y")));
	}

	/**
	 * Valid order: T, S, followed by the built-in passes.
	 */
	@Test
	void startPassReferencedByAnotherPass() {
		assertValidMerge(asList("a", "b"), asList(
				info("S").after(JadxPassInfo.START),
				info("T").before("S")));
	}

	/**
	 * Valid order: the built-in passes, followed by E, F.
	 */
	@Test
	void endPassReferencedByAnotherPass() {
		assertValidMerge(asList("a", "b"), asList(
				info("E").before(JadxPassInfo.END),
				info("F").after("E")));
	}

	/**
	 * Exhaustive check with built-in passes 'a', 'b' and plugin passes 'x', 'y', 'z'. Every order of
	 * the five passes that keeps 'a' before 'b' is taken as a target, and each plugin pass declares
	 * 0, 1 or 2 constraints that agree with it: 60 * 11 * 11 * 11 = 79,860 setups, all satisfiable.
	 */
	@Test
	void smallSatisfiableSetups() {
		List<String> builtIns = asList("a", "b");
		List<String> plugins = asList("x", "y", "z");
		List<List<String>> targets = new ArrayList<>();
		collectPermutations(new ArrayList<>(), asList("a", "b", "x", "y", "z"), targets);
		targets.removeIf(order -> order.indexOf("a") > order.indexOf("b"));
		int total = 0;
		List<String> failures = new ArrayList<>();
		for (List<String> target : targets) {
			List<List<List<String>>> options = new ArrayList<>();
			for (String plugin : plugins) {
				List<String> others = new ArrayList<>(target);
				others.remove(plugin);
				options.add(subsetsUpToTwo(others));
			}
			for (List<String> xDeps : options.get(0)) {
				for (List<String> yDeps : options.get(1)) {
					for (List<String> zDeps : options.get(2)) {
						total++;
						List<OrderedJadxPassInfo> passes = new ArrayList<>();
						List<List<String>> deps = asList(xDeps, yDeps, zDeps);
						for (int i = 0; i < plugins.size(); i++) {
							String plugin = plugins.get(i);
							OrderedJadxPassInfo info = info(plugin);
							for (String dep : deps.get(i)) {
								if (target.indexOf(dep) < target.indexOf(plugin)) {
									info.after(dep);
								} else {
									info.before(dep);
								}
							}
							passes.add(info);
						}
						try {
							assertValidMerge(builtIns, passes);
						} catch (Throwable e) {
							failures.add(describe(passes) + " -> " + String.valueOf(e.getMessage()).split("\n")[0]);
						}
					}
				}
			}
		}
		assertThat(total).isEqualTo(79_860);
		assertThat(failures)
				.as("%d of %d satisfiable setups failed, first 5: %s", failures.size(), total,
						failures.subList(0, Math.min(5, failures.size())))
				.isEmpty();
	}

	/**
	 * Merge the passes and check the result against their declared constraints. A repeated built-in
	 * name resolves to its last occurrence, as in {@link PassMerge}.
	 */
	private static List<String> assertValidMerge(List<String> builtIns, List<OrderedJadxPassInfo> infos) {
		List<IDexTreeVisitor> visitors = ListUtils.map(builtIns, PassMergeOrderingBugsTest::visitor);
		List<JadxPass> passes = ListUtils.map(infos, PassMergeOrderingBugsTest::pass);
		new PassMerge(visitors).merge(passes, p -> new DecompilePassWrapper((JadxDecompilePass) p));
		List<String> result = ListUtils.map(visitors, IDexTreeVisitor::getName);

		assertThat(result).as("all passes present").hasSize(builtIns.size() + infos.size());
		List<String> resultBuiltIns = new ArrayList<>(result);
		resultBuiltIns.removeAll(ListUtils.map(infos, JadxPassInfo::getName));
		assertThat(resultBuiltIns).as("built-in passes keep their order").isEqualTo(builtIns);
		int firstBuiltIn = result.indexOf(builtIns.get(0));
		int lastBuiltIn = result.lastIndexOf(builtIns.get(builtIns.size() - 1));
		for (OrderedJadxPassInfo info : infos) {
			String name = info.getName();
			int pos = result.indexOf(name);
			for (String dep : info.runAfter()) {
				if (dep.equals(JadxPassInfo.START)) {
					assertThat(pos).as("START pass %s before built-in passes in %s", name, result).isLessThan(firstBuiltIn);
				} else {
					assertThat(pos).as("%s after %s in %s", name, dep, result).isGreaterThan(result.lastIndexOf(dep));
				}
			}
			for (String dep : info.runBefore()) {
				if (dep.equals(JadxPassInfo.END)) {
					assertThat(pos).as("END pass %s after built-in passes in %s", name, result).isGreaterThan(lastBuiltIn);
				} else {
					assertThat(pos).as("%s before %s in %s", name, dep, result).isLessThan(result.lastIndexOf(dep));
				}
			}
		}
		return result;
	}

	private static List<String> realPipeline() {
		return ListUtils.map(Jadx.getPassesList(new JadxArgs()), IDexTreeVisitor::getName);
	}

	private static OrderedJadxPassInfo info(String name) {
		return new OrderedJadxPassInfo(name, name);
	}

	private static String describe(List<OrderedJadxPassInfo> passes) {
		return ListUtils.map(passes, p -> p.getName() + "(after " + p.runAfter() + ", before " + p.runBefore() + ')')
				.toString();
	}

	private static void collectPermutations(List<String> prefix, List<String> rest, List<List<String>> out) {
		if (rest.isEmpty()) {
			out.add(prefix);
			return;
		}
		for (String next : rest) {
			List<String> newPrefix = new ArrayList<>(prefix);
			newPrefix.add(next);
			List<String> newRest = new ArrayList<>(rest);
			newRest.remove(next);
			collectPermutations(newPrefix, newRest, out);
		}
	}

	private static List<List<String>> subsetsUpToTwo(List<String> items) {
		List<List<String>> subsets = new ArrayList<>();
		subsets.add(emptyList());
		for (int i = 0; i < items.size(); i++) {
			subsets.add(singletonList(items.get(i)));
			for (int j = i + 1; j < items.size(); j++) {
				subsets.add(asList(items.get(i), items.get(j)));
			}
		}
		return subsets;
	}

	private static IDexTreeVisitor visitor(String name) {
		return new AbstractVisitor() {
			@Override
			public String getName() {
				return name;
			}
		};
	}

	private static JadxPass pass(JadxPassInfo info) {
		return new JadxDecompilePass() {
			@Override
			public void init(RootNode root) {
			}

			@Override
			public boolean visit(ClassNode cls) {
				return false;
			}

			@Override
			public void visit(MethodNode mth) {
			}

			@Override
			public JadxPassInfo getInfo() {
				return info;
			}
		};
	}
}
