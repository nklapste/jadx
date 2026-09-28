package jadx.core.utils;

import java.util.ArrayList;
import java.util.List;

import org.junit.jupiter.api.Test;

import jadx.api.impl.passes.DecompilePassWrapper;
import jadx.api.plugins.pass.JadxPass;
import jadx.api.plugins.pass.JadxPassInfo;
import jadx.api.plugins.pass.impl.OrderedJadxPassInfo;
import jadx.api.plugins.pass.impl.SimpleJadxPassInfo;
import jadx.api.plugins.pass.types.JadxDecompilePass;
import jadx.core.dex.nodes.ClassNode;
import jadx.core.dex.nodes.MethodNode;
import jadx.core.dex.nodes.RootNode;
import jadx.core.dex.visitors.AbstractVisitor;
import jadx.core.dex.visitors.IDexTreeVisitor;
import jadx.core.utils.exceptions.JadxRuntimeException;

import static jadx.tests.api.utils.assertj.JadxAssertions.assertThat;
import static java.util.Arrays.asList;
import static java.util.Collections.emptyList;
import static java.util.Collections.singletonList;
import static org.assertj.core.api.Assertions.catchThrowable;

class PassMergeTest {

	@Test
	public void testSimple() {
		List<String> base = asList("a", "b", "c");
		check(base, mockPass("x"), asList("a", "b", "c", "x"));
		check(base, mockPass(mockInfo("x").after(JadxPassInfo.START)), asList("x", "a", "b", "c"));
		check(base, mockPass(mockInfo("x").before(JadxPassInfo.END)), asList("a", "b", "c", "x"));
	}

	@Test
	public void testSingle() {
		List<String> base = asList("a", "b", "c");
		check(base, mockPass(mockInfo("x").after("a")), asList("a", "x", "b", "c"));
		check(base, mockPass(mockInfo("x").before("c")), asList("a", "b", "x", "c"));
		check(base, mockPass(mockInfo("x").before("a")), asList("x", "a", "b", "c"));
		check(base, mockPass(mockInfo("x").after("c")), asList("a", "b", "c", "x"));
	}

	@Test
	public void testMulti() {
		List<String> base = asList("a", "b", "c");
		JadxPass x = mockPass(mockInfo("x").after("a"));
		JadxPass y = mockPass(mockInfo("y").after("a"));
		JadxPass z = mockPass(mockInfo("z").before("b"));
		check(base, asList(x, y, z), asList("a", "y", "x", "z", "b", "c"));
	}

	@Test
	public void testMultiWithDeps() {
		List<String> base = asList("a", "b", "c");
		JadxPass x = mockPass(mockInfo("x").after("a"));
		JadxPass y = mockPass(mockInfo("y").after("x"));
		JadxPass z = mockPass(mockInfo("z").before("b").after("y"));
		check(base, asList(x, y, z), asList("a", "x", "y", "z", "b", "c"));
	}

	@Test
	public void testMultiWithDeps2() {
		List<String> base = asList("a", "b", "c");
		JadxPass x = mockPass(mockInfo("x").before("y"));
		JadxPass y = mockPass(mockInfo("y").before("b"));
		JadxPass z = mockPass(mockInfo("z").after("y"));
		check(base, asList(x, y, z), asList("a", "x", "y", "z", "b", "c"));
	}

	@Test
	public void testMultiWithDeps3() {
		List<String> base = asList("a", "b", "c");
		JadxPass x = mockPass(mockInfo("x"));
		JadxPass y = mockPass(mockInfo("y").after("x").before("b"));
		check(base, asList(x, y), asList("a", "x", "y", "b", "c"));
	}

	@Test
	public void testManyInterdependentPasses() {
		// Regression test for "Comparison method violates its general contract!": passes used to be
		// sorted with an invalid Comparator, which TimSort rejects once there are enough of them.
		// The constraints are dense but acyclic (lower index runs first), so a valid order exists.
		List<String> base = asList("a", "b", "c", "d", "e");
		int n = 57;
		List<JadxPass> passes = new ArrayList<>();
		List<String[]> constraints = new ArrayList<>(); // {first, second}: first must run before second
		for (int i = 0; i < n; i++) {
			OrderedJadxPassInfo info = mockInfo("p" + i);
			// half the passes anchor to a built-in visitor
			if (i % 2 == 0) {
				String anchor = base.get(i % base.size());
				info.after(anchor);
				constraints.add(new String[] { anchor, "p" + i });
			}
			for (int j = 0; j < i; j++) {
				if ((i * 7 + j * 13) % 3 == 0) {
					info.after("p" + j);
					constraints.add(new String[] { "p" + j, "p" + i });
				}
			}
			for (int k = i + 1; k < n; k++) {
				if ((i * 5 + k * 11) % 4 == 0) {
					info.before("p" + k);
					constraints.add(new String[] { "p" + i, "p" + k });
				}
			}
			passes.add(mockPass(info));
		}
		List<String> result = merge(base, passes);
		assertThat(result).hasSize(base.size() + n);
		for (String[] c : constraints) {
			assertThat(result.indexOf(c[0]))
					.as("%s must run before %s", c[0], c[1])
					.isLessThan(result.indexOf(c[1]));
		}
	}

	@Test
	public void testSatisfiableOrderNotBlockedByInsertionOrder() {
		// A valid order exists (a, x, z, y, b), but inserting passes one at a time puts 'y' before
		// 'x' before 'z' is considered, which used to end in a false "Conflict order requirements".
		List<String> base = asList("a", "b");
		JadxPass x = mockPass(mockInfo("x").before("b"));
		JadxPass y = mockPass(mockInfo("y").after("a"));
		JadxPass z = mockPass(mockInfo("z").after("x").before("y"));
		check(base, asList(x, y, z), asList("a", "x", "z", "y", "b"));
	}

	@Test
	public void testSmallSatisfiableSetNoFalseConflict() {
		// valid order: a, x, y, z, b - used to fail with "Conflict order requirements for pass: y"
		List<String> base = asList("a", "b");
		JadxPass x = mockPass(mockInfo("x").before("y"));
		JadxPass y = mockPass(mockInfo("y"));
		JadxPass z = mockPass(mockInfo("z").after("a").after("y"));
		check(base, asList(x, y, z), asList("a", "x", "y", "z", "b"));
	}

	@Test
	public void testRepeatedBuiltInNames() {
		// The real pipeline repeats some built-in passes (e.g. CodeShrinkVisitor). A repeated name
		// resolves to its last occurrence: 'w' runs after the second 'd', not the first.
		List<String> base = asList("a", "d", "b", "d");
		JadxPass x = mockPass(mockInfo("x").before("b"));
		JadxPass y = mockPass(mockInfo("y").after("a"));
		JadxPass z = mockPass(mockInfo("z").after("x").before("y"));
		JadxPass w = mockPass(mockInfo("w").after("d"));
		check(base, asList(x, y, z, w), asList("a", "x", "z", "y", "d", "b", "d", "w"));
	}

	@Test
	public void testRunBeforePassPlacedRightBeforeItsAnchor() {
		// 'w' only has to run before 'd': it must not be pulled in front of 'b' and 'c'
		List<String> base = asList("a", "b", "c", "d");
		JadxPass w = mockPass(mockInfo("w").before("d"));
		JadxPass x = mockPass(mockInfo("x").before("b"));
		JadxPass y = mockPass(mockInfo("y").after("a"));
		JadxPass z = mockPass(mockInfo("z").after("x").before("y"));
		check(base, asList(w, x, y, z), asList("a", "x", "z", "y", "b", "c", "w", "d"));
	}

	@Test
	public void testStartPassRunsFirst() {
		List<String> base = asList("a", "b", "c");
		JadxPass x = mockPass(mockInfo("x").before("b"));
		JadxPass y = mockPass(mockInfo("y").after("a"));
		JadxPass z = mockPass(mockInfo("z").after("x").before("y"));
		JadxPass s = mockPass(mockInfo("s").after(JadxPassInfo.START));
		check(base, asList(x, y, z, s), asList("s", "a", "x", "z", "y", "b", "c"));
	}

	@Test
	public void testStartAndEndReferencedByOtherPasses() {
		List<String> base = asList("a", "b");
		// END pass that another pass runs after
		check(base, asList(mockPass(mockInfo("e").before(JadxPassInfo.END)), mockPass(mockInfo("f").after("e"))),
				asList("a", "b", "e", "f"));
		// START pass that another pass runs before
		check(base, asList(mockPass(mockInfo("s").after(JadxPassInfo.START)), mockPass(mockInfo("t").before("s"))),
				asList("t", "s", "a", "b"));
	}

	@Test
	public void testStartAndEndOnSamePass() {
		// START and END are placement hints, not constraints: START wins, as it always did
		List<String> base = asList("a", "b", "c");
		check(base, mockPass(mockInfo("x").after(JadxPassInfo.START).before(JadxPassInfo.END)),
				asList("x", "a", "b", "c"));
	}

	@Test
	public void testMultipleStartPasses() {
		// the later registered START pass runs first, as it always did
		List<String> base = asList("a", "b", "c");
		JadxPass s1 = mockPass(mockInfo("s1").after(JadxPassInfo.START));
		JadxPass s2 = mockPass(mockInfo("s2").after(JadxPassInfo.START));
		check(base, asList(s1, s2), asList("s2", "s1", "a", "b", "c"));
	}

	@Test
	public void testRunBeforePassWithCustomTarget() {
		// 'q' only has to run before 'y', which runs right after 'a': both stay right after 'a'
		List<String> base = asList("a", "b", "c");
		JadxPass y = mockPass(mockInfo("y").after("a"));
		JadxPass q = mockPass(mockInfo("q").before("y"));
		check(base, asList(y, q), asList("a", "q", "y", "b", "c"));
		check(base, asList(q, y), asList("a", "q", "y", "b", "c"));
	}

	@Test
	public void testSelfReferenceIgnored() {
		List<String> base = asList("a", "b", "c");
		check(base, mockPass(mockInfo("x").after("x")), asList("a", "b", "c", "x"));
		check(base, mockPass(mockInfo("x").after("a").before("x")), asList("a", "x", "b", "c"));
	}

	@Test
	public void testBuiltInNameTakesPrecedence() {
		// a custom pass named like a built-in must not capture references to the built-in
		List<String> base = asList("a", "b", "c");
		JadxPass customB = mockPass(mockInfo("b").after("a"));
		JadxPass z = mockPass(mockInfo("z").after("b"));
		check(base, asList(customB, z), asList("a", "b", "b", "z", "c"));
	}

	@Test
	public void testCycleThroughBuiltInPasses() {
		List<String> base = asList("a", "b", "c");
		JadxPass x = mockPass(mockInfo("x").before("a").after("c"));
		assertMergeFails(base, singletonList(x), "cyclic dependencies",
				"x (runAfter: [c], runBefore: [a])", "through built-in passes: [a .. c]");
	}

	@Test
	public void testConstraintListOrderDoesNotMatter() {
		List<String> base = asList("a", "b", "c");
		List<String> expected = asList("s", "p1", "q", "a", "b", "c", "u");
		check(base, asList(mockPass(mockInfo("p1")), mockPass(mockInfo("s").after(JadxPassInfo.START)),
				mockPass(mockInfo("u")), mockPass(mockInfo("q").after("p1").after("s"))), expected);
		check(base, asList(mockPass(mockInfo("p1")), mockPass(mockInfo("s").after(JadxPassInfo.START)),
				mockPass(mockInfo("u")), mockPass(mockInfo("q").after("s").after("p1"))), expected);
	}

	@Test
	public void testTiesKeepHistoricalOrder() {
		List<String> base = asList("a", "b", "c");
		// END passes keep registration order, also when anchored after a built-in pass
		check(base, asList(mockPass(mockInfo("x").after("a").before(JadxPassInfo.END)),
				mockPass(mockInfo("y").after("a").before(JadxPassInfo.END))),
				asList("a", "b", "c", "x", "y"));
		// END passes and unconstrained passes are appended in registration order
		check(base, asList(mockPass(mockInfo("e").before(JadxPassInfo.END)), mockPass(mockInfo("u"))),
				asList("a", "b", "c", "e", "u"));
		check(base, asList(mockPass(mockInfo("x").after("a").before(JadxPassInfo.END)), mockPass(mockInfo("u"))),
				asList("a", "b", "c", "x", "u"));
		// passes after the same START pass: the later registered one runs first
		check(base, asList(mockPass(mockInfo("s").after(JadxPassInfo.START)),
				mockPass(mockInfo("q").after("s")), mockPass(mockInfo("r").after("s"))),
				asList("s", "r", "q", "a", "b", "c"));
		// 'y' only has to run before 'q': it goes after the unrelated 'x', right before 'q'
		check(base, asList(mockPass(mockInfo("y").before("b")), mockPass(mockInfo("x").after("a")),
				mockPass(mockInfo("q").after("x").after("y"))),
				asList("a", "x", "y", "q", "b", "c"));
	}

	@Test
	public void testCycleErrorListsOnlyPassesOnTheCycle() {
		List<String> base = asList("a", "b", "c", "d");
		JadxPass x = mockPass(mockInfo("x").before("b").after("c"));
		// 'a' and 'd' are not on the cycle b -> c -> x -> b
		assertMergeFails(base, singletonList(x), "x (runAfter: [c], runBefore: [b])", "through built-in passes: [b .. c]");
	}

	@Test
	public void testCycleErrorWithSeparateCycles() {
		// two cycles: a -> b -> x -> a and d -> e -> y -> d; 'c' is not involved
		List<String> base = asList("a", "b", "c", "d", "e");
		JadxPass x = mockPass(mockInfo("x").after("b").before("a"));
		JadxPass y = mockPass(mockInfo("y").after("e").before("d"));
		assertMergeFails(base, asList(x, y), "through built-in passes: [a .. b, d .. e]");
	}

	@Test
	public void testEndPassIsLowerBoundForFollowers() {
		// 'X' follows 'b1' and END pass 'E' (after 'b6'): it can only run after 'b6', so 'L' (only
		// before 'X') is placed right before it, not right after 'b1'
		List<String> base = asList("b0", "b1", "b2", "b3", "b4", "b5", "b6", "b7");
		JadxPass e = mockPass(mockInfo("E").after("b6").before(JadxPassInfo.END));
		JadxPass x = mockPass(mockInfo("X").after("b1").after("E"));
		JadxPass l = mockPass(mockInfo("L").before("X"));
		check(base, asList(e, x, l), asList("b0", "b1", "b2", "b3", "b4", "b5", "b6", "L", "E", "X", "b7"));
	}

	@Test
	public void testFollowerOfEndPassStaysAtEnd() {
		List<String> base = asList("a", "b", "c");
		JadxPass e = mockPass(mockInfo("E").after("a").before(JadxPassInfo.END));
		JadxPass y = mockPass(mockInfo("Y").after("E"));
		check(base, asList(e, y), asList("a", "b", "c", "E", "Y"));
	}

	@Test
	public void testUnknownNamesInOtherListOfStartOrEndPass() {
		// the other list of a START or END pass used to be ignored: unknown names there are skipped
		List<String> base = asList("a", "b", "c");
		check(base, mockPass(mockInfo("x").after(JadxPassInfo.START).before("gone")), asList("x", "a", "b", "c"));
		check(base, mockPass(mockInfo("x").before(JadxPassInfo.END).after("gone")), asList("a", "b", "c", "x"));
	}

	@Test
	public void testEndPassFollowedByEarlyPass() {
		// 'N' runs right after 'a' and has to follow END pass 'E', so 'E' moves up right before it
		List<String> base = asList("a", "b", "c", "d");
		JadxPass e = mockPass(mockInfo("E").before(JadxPassInfo.END));
		JadxPass n = mockPass(mockInfo("N").after("E").after("a"));
		check(base, asList(e, n), asList("a", "E", "N", "b", "c", "d"));
	}

	@Test
	public void testEndPassThatMustPrecedeBuiltIn() {
		// 'P' follows END pass 'E' and must run before 'c': 'E' goes right before 'P', and 'L'
		// (only before 'd') does not jump ahead of 'c'
		List<String> base = asList("a", "b", "c", "d");
		JadxPass e = mockPass(mockInfo("E").before(JadxPassInfo.END));
		JadxPass p = mockPass(mockInfo("P").after("E").before("c"));
		JadxPass l = mockPass(mockInfo("L").before("d"));
		check(base, asList(e, p, l), asList("a", "b", "E", "P", "c", "L", "d"));
	}

	@Test
	public void testStartPassThatMustFollowBuiltIn() {
		// START pass 's' has to follow 'Z' (after 'c'): it runs right after it, with 'L' right before 's'
		List<String> base = asList("a", "b", "c", "d");
		JadxPass s = mockPass(mockInfo("s").after(JadxPassInfo.START));
		JadxPass z = mockPass(mockInfo("Z").after("c").before("s"));
		JadxPass l = mockPass(mockInfo("L").before("s"));
		check(base, asList(s, z, l), asList("a", "b", "c", "Z", "L", "s", "d"));
	}

	@Test
	public void testStartAndEndAreHintsOnlyAsSingleEntry() {
		List<String> base = asList("a", "b");
		// mixed with other names, 'start' and 'end' are pass names
		assertMergeFails(base, singletonList(mockPass(mockInfo("x").after(JadxPassInfo.START).after("a"))),
				"Ordering pass not found: start, listed in 'runAfter' of pass: x",
				"placement hints only as the single entry");
		assertMergeFails(base, singletonList(mockPass(mockInfo("x").before(JadxPassInfo.START))),
				"Ordering pass not found: start, listed in 'runBefore' of pass: x",
				"placement hints only as the single entry");
	}

	@Test
	public void testCustomPassNamedStart() {
		// a pass named 'start' can be referenced by name in a list with other entries
		List<String> base = asList("a", "b", "c");
		JadxPass start = mockPass(mockInfo(JadxPassInfo.START).after("a"));
		JadxPass y = mockPass(mockInfo("y").after(JadxPassInfo.START).after("b"));
		check(base, asList(start, y), asList("a", "start", "b", "y", "c"));
	}

	@Test
	public void testDuplicateNames() {
		List<String> base = asList("a", "b");
		JadxPass x1 = mockPass(mockInfo("x").after("a"));
		JadxPass x2 = mockPass(mockInfo("x").before("b"));
		assertMergeFails(base, asList(x1, x2), "Duplicate pass name: x");
	}

	@Test
	public void testAllSmallSatisfiableConstraintSets() {
		// Exhaustive check over a small space: built-ins 'a', 'b' and custom passes 'x', 'y', 'z'.
		// Every arrangement of the five names that keeps 'a' before 'b' is a valid target order.
		// For each one, every custom pass declares 0, 1 or 2 constraints towards other names, with
		// runAfter/runBefore taken from the target order, so every constraint set is satisfiable.
		// Each set must merge without error and honour every declared constraint.
		List<String> base = asList("a", "b");
		List<String> custom = asList("x", "y", "z");
		List<List<String>> targetOrders = new ArrayList<>();
		collectPermutations(new ArrayList<>(), asList("a", "b", "x", "y", "z"), targetOrders);
		targetOrders.removeIf(order -> order.indexOf("a") > order.indexOf("b"));

		List<String> failures = new ArrayList<>();
		int cases = 0;
		for (List<String> target : targetOrders) {
			List<List<List<String>>> options = new ArrayList<>(); // per custom pass: its constraint targets
			for (String pass : custom) {
				List<String> others = new ArrayList<>(target);
				others.remove(pass);
				options.add(subsetsUpToTwo(others));
			}
			for (List<String> xDeps : options.get(0)) {
				for (List<String> yDeps : options.get(1)) {
					for (List<String> zDeps : options.get(2)) {
						cases++;
						String failure = checkCase(base, target, custom, asList(xDeps, yDeps, zDeps));
						if (failure != null && failures.size() < 10) {
							failures.add(failure);
						}
					}
				}
			}
		}
		assertThat(targetOrders).hasSize(60);
		assertThat(cases).isEqualTo(60 * 11 * 11 * 11);
		assertThat(failures).as("failed cases (first 10)").isEmpty();
	}

	/**
	 * Merge one constraint set and verify it; returns a description of the problem or null if valid.
	 */
	private String checkCase(List<String> base, List<String> target, List<String> custom,
			List<List<String>> depsPerPass) {
		List<JadxPass> passes = new ArrayList<>();
		List<String[]> constraints = new ArrayList<>(); // {first, second}: first must run before second
		for (int i = 0; i < custom.size(); i++) {
			String pass = custom.get(i);
			OrderedJadxPassInfo info = mockInfo(pass);
			for (String dep : depsPerPass.get(i)) {
				if (target.indexOf(dep) < target.indexOf(pass)) {
					info.after(dep);
					constraints.add(new String[] { dep, pass });
				} else {
					info.before(dep);
					constraints.add(new String[] { pass, dep });
				}
			}
			passes.add(mockPass(info));
		}
		List<String> result;
		try {
			result = merge(base, passes);
		} catch (Exception e) {
			return describeCase(target, constraints) + " -> threw " + String.valueOf(e).split("\n")[0];
		}
		if (result.size() != base.size() + custom.size() || result.indexOf("a") > result.indexOf("b")) {
			return describeCase(target, constraints) + " -> bad result " + result;
		}
		for (String[] c : constraints) {
			if (result.indexOf(c[0]) > result.indexOf(c[1])) {
				return describeCase(target, constraints) + " -> " + c[0] + " not before " + c[1] + " in " + result;
			}
		}
		return null;
	}

	private static String describeCase(List<String> target, List<String[]> constraints) {
		return "target " + target + ", constraints " + ListUtils.map(constraints, c -> c[0] + "<" + c[1]);
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

	@Test
	public void testLoop() {
		List<String> base = asList("a", "b", "c");
		JadxPass x = mockPass(mockInfo("x").before("y"));
		JadxPass y = mockPass(mockInfo("y").before("x"));
		assertMergeFails(base, asList(x, y), "cyclic dependencies");
	}

	private void check(List<String> visitorNames, JadxPass pass, List<String> result) {
		check(visitorNames, singletonList(pass), result);
	}

	private void check(List<String> visitorNames, List<JadxPass> passes, List<String> result) {
		assertThat(merge(visitorNames, passes)).isEqualTo(result);
	}

	/**
	 * Merge passes into built-in passes with the given names and return the resulting pass names.
	 */
	private static List<String> merge(List<String> visitorNames, List<JadxPass> passes) {
		List<IDexTreeVisitor> visitors = ListUtils.map(visitorNames, PassMergeTest::mockVisitor);
		new PassMerge(visitors).merge(passes, p -> new DecompilePassWrapper((JadxDecompilePass) p));
		return ListUtils.map(visitors, IDexTreeVisitor::getName);
	}

	private static void assertMergeFails(List<String> visitorNames, List<JadxPass> passes, String... messageParts) {
		Throwable thrown = catchThrowable(() -> merge(visitorNames, passes));
		assertThat(thrown).isInstanceOf(JadxRuntimeException.class);
		for (String part : messageParts) {
			assertThat(thrown).hasMessageContaining(part);
		}
	}

	private static IDexTreeVisitor mockVisitor(String name) {
		return new AbstractVisitor() {
			@Override
			public String getName() {
				return name;
			}
		};
	}

	private JadxPass mockPass(String name) {
		return mockPass(new SimpleJadxPassInfo(name));
	}

	private OrderedJadxPassInfo mockInfo(String name) {
		return new OrderedJadxPassInfo(name, name);
	}

	private JadxPass mockPass(JadxPassInfo info) {
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

			@Override
			public String toString() {
				return info.getName();
			}
		};
	}
}
