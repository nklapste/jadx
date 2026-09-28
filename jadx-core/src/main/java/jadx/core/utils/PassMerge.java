package jadx.core.utils;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Queue;
import java.util.function.Function;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import jadx.api.plugins.pass.JadxPass;
import jadx.api.plugins.pass.JadxPassInfo;
import jadx.core.dex.visitors.IDexTreeVisitor;
import jadx.core.utils.exceptions.JadxRuntimeException;

/**
 * Merge custom (plugin) passes into a list of built-in passes, honouring their
 * {@link JadxPassInfo#runAfter()} and {@link JadxPassInfo#runBefore()} constraints.
 * <p>
 * All passes and constraints form one graph: built-in passes are chained in their existing order
 * and every constraint adds an edge. The graph is sorted with Kahn's algorithm, so any satisfiable
 * set of constraints gets a valid order and only real cycles are rejected.
 * <p>
 * Among the valid orders, every pass gets a position on the built-in timeline and ready passes are
 * placed by position:
 * <ul>
 * <li>a pass that runs after a built-in pass or a {@link JadxPassInfo#START} pass (directly or
 * through other passes, except END passes) is placed as early as possible, after every pass it
 * follows;</li>
 * <li>other passes are placed as late as possible, right before the first pass they have to
 * precede, or else right after the passes they follow;</li>
 * <li>a START pass is placed as early as possible: first, unless it has to follow other
 * passes;</li>
 * <li>an {@link JadxPassInfo#END} pass is placed as late as possible: last, unless other passes
 * have to follow it;</li>
 * <li>unconstrained passes are appended at the end.</li>
 * </ul>
 * At the same position, passes placed as early as possible come before passes placed as late as
 * possible. START passes and passes placed as early as possible keep the historical order (the
 * later registered pass runs first); other passes keep registration order.
 * <p>
 * As before, START and END are hints only when they are the single entry of {@code runAfter} and
 * {@code runBefore} (START wins if a pass declares both); anywhere else they are pass names. The
 * other list of a START or END pass is honoured, but unknown names in it are ignored with a
 * warning, as that list used to be ignored. A built-in name that appears several times (e.g.
 * CodeShrinkVisitor) resolves to its last occurrence. Built-in names take precedence over custom
 * passes with the same name. A pass referencing itself is ignored.
 */
public class PassMerge {
	private static final Logger LOG = LoggerFactory.getLogger(PassMerge.class);

	private final List<IDexTreeVisitor> visitors;

	public PassMerge(List<IDexTreeVisitor> visitors) {
		this.visitors = visitors;
	}

	public void merge(List<JadxPass> customPasses, Function<JadxPass, IDexTreeVisitor> wrap) {
		if (Utils.isEmpty(customPasses)) {
			return;
		}
		List<IDexTreeVisitor> merged = new Graph(visitors, customPasses, wrap).sort();
		// replace only on success, so a failed merge leaves the pass list untouched
		visitors.clear();
		visitors.addAll(merged);
	}

	/**
	 * Nodes are built-in passes (ids {@code 0 .. builtInCount - 1}, in pipeline order) followed by
	 * custom passes in registration order.
	 */
	private static final class Graph {
		// placement kinds, in the order they are placed when they share a position
		private static final int START = 0;
		private static final int EARLY = 1; // as early as possible after the passes it follows
		private static final int LATE = 2; // as late as possible before the first pass it precedes
		private static final int END = 3; // END hint or unconstrained

		private final List<IDexTreeVisitor> nodes = new ArrayList<>();
		private final List<String> names = new ArrayList<>();
		private final List<JadxPassInfo> customInfos = new ArrayList<>();
		private final int builtInCount;
		private final int total;
		private final int endPosition;
		private final List<List<Integer>> successors = new ArrayList<>();
		private final List<List<Integer>> predecessors = new ArrayList<>();
		private final boolean[] startPass;
		private final boolean[] endPass;
		// placement, filled by computePositions()
		private final int[] position;
		private final int[] kind;
		private final boolean[] placed;

		Graph(List<IDexTreeVisitor> builtInPasses, List<JadxPass> customPasses, Function<JadxPass, IDexTreeVisitor> wrap) {
			builtInCount = builtInPasses.size();
			total = builtInCount + customPasses.size();
			endPosition = builtInPosition(builtInCount);
			for (IDexTreeVisitor pass : builtInPasses) {
				nodes.add(pass);
				names.add(pass.getName());
			}
			for (JadxPass pass : customPasses) {
				nodes.add(wrap.apply(pass));
				names.add(pass.getInfo().getName());
				customInfos.add(pass.getInfo());
			}
			for (int i = 0; i < total; i++) {
				successors.add(new ArrayList<>());
				predecessors.add(new ArrayList<>());
			}
			startPass = new boolean[total];
			endPass = new boolean[total];
			position = new int[total];
			kind = new int[total];
			placed = new boolean[total];
			addEdges();
		}

		private boolean isBuiltIn(int node) {
			return node < builtInCount;
		}

		/**
		 * Built-in pass {@code i} sits at {@code 4i + 2}, leaving room for custom passes right before
		 * ({@code 4i + 1}) and right after ({@code 4i + 3}) it.
		 */
		private static int builtInPosition(int index) {
			return 4 * index + 2;
		}

		private JadxPassInfo info(int customNode) {
			return customInfos.get(customNode - builtInCount);
		}

		private void addEdges() {
			for (int i = 1; i < builtInCount; i++) {
				addEdge(i - 1, i);
			}
			Map<String, Integer> nodeByName = buildNameIndex();
			for (int node = builtInCount; node < total; node++) {
				JadxPassInfo info = info(node);
				// START and END are hints only as the single entry of their list; START wins if both
				startPass[node] = ListUtils.isSingleElement(info.runAfter(), JadxPassInfo.START);
				boolean endHint = ListUtils.isSingleElement(info.runBefore(), JadxPassInfo.END);
				endPass[node] = endHint && !startPass[node];
				// the other list of a START or END pass used to be ignored: don't fail on unknown names
				if (!startPass[node]) {
					for (int prev : resolveAll(nodeByName, info.runAfter(), "runAfter", info, endHint)) {
						addEdge(prev, node);
					}
				}
				if (!endHint) {
					for (int next : resolveAll(nodeByName, info.runBefore(), "runBefore", info, startPass[node])) {
						addEdge(node, next);
					}
				}
			}
		}

		private Map<String, Integer> buildNameIndex() {
			Map<String, Integer> nodeByName = new HashMap<>();
			for (int node = builtInCount; node < total; node++) {
				String name = names.get(node);
				if (nodeByName.put(name, node) != null) {
					throw new JadxRuntimeException("Duplicate pass name: " + name);
				}
			}
			// built-in names take precedence; a repeated built-in name resolves to its last occurrence
			for (int node = 0; node < builtInCount; node++) {
				nodeByName.put(names.get(node), node);
			}
			return nodeByName;
		}

		/**
		 * Node ids for pass names. If {@code lenient}, unknown names are logged and skipped.
		 */
		private List<Integer> resolveAll(Map<String, Integer> nodeByName, List<String> passNames, String listName,
				JadxPassInfo info, boolean lenient) {
			List<Integer> resolved = new ArrayList<>(passNames.size());
			for (String name : passNames) {
				Integer node = nodeByName.get(name);
				if (node != null) {
					resolved.add(node);
				} else if (lenient) {
					LOG.warn("Ignoring unknown pass '{}' listed in '{}' of pass: {}", name, listName, info.getName());
				} else {
					throw passNotFound(name, listName, info);
				}
			}
			return resolved;
		}

		private JadxRuntimeException passNotFound(String name, String listName, JadxPassInfo info) {
			String hintNote = "";
			if (name.equals(JadxPassInfo.START) || name.equals(JadxPassInfo.END)) {
				hintNote = "\n note: '" + JadxPassInfo.START + "' and '" + JadxPassInfo.END + "' are placement hints"
						+ " only as the single entry of 'runAfter' and 'runBefore' respectively";
			}
			return new JadxRuntimeException("Ordering pass not found: " + name
					+ ", listed in '" + listName + "' of pass: " + info.getName()
					+ hintNote
					+ "\n all passes: " + names);
		}

		private void addEdge(int from, int to) {
			if (from == to) {
				return; // a pass referencing itself
			}
			successors.get(from).add(to);
			predecessors.get(to).add(from);
		}

		List<IDexTreeVisitor> sort() {
			List<Integer> order = kahn(new ArrayDeque<>());
			if (order.size() != total) {
				throw cycleError(order);
			}
			computePositions(order);
			Comparator<Integer> placement = Comparator.<Integer>comparingInt(n -> position[n])
					.thenComparingInt(n -> kind[n])
					.thenComparingInt(n -> kind[n] <= EARLY ? -n : n); // START/EARLY: later registered first
			List<IDexTreeVisitor> result = new ArrayList<>(total);
			for (int node : kahn(new PriorityQueue<>(placement))) {
				result.add(nodes.get(node));
			}
			return result;
		}

		/**
		 * Kahn's algorithm, taking ready nodes in the order of the given queue. Returns fewer than
		 * {@code total} nodes if the graph has a cycle.
		 */
		private List<Integer> kahn(Queue<Integer> ready) {
			int[] remaining = new int[total];
			for (int node = 0; node < total; node++) {
				remaining[node] = predecessors.get(node).size();
				if (remaining[node] == 0) {
					ready.add(node);
				}
			}
			List<Integer> order = new ArrayList<>(total);
			while (!ready.isEmpty()) {
				int node = ready.poll();
				order.add(node);
				for (int next : successors.get(node)) {
					if (--remaining[next] == 0) {
						ready.add(next);
					}
				}
			}
			return order;
		}

		private void computePositions(List<Integer> order) {
			// earliest position of every pass: after all built-in and START passes it follows
			int[] earliest = new int[total];
			// follows a built-in or START pass, other than only through END passes
			boolean[] anchored = new boolean[total];
			for (int node : order) {
				anchored[node] = isBuiltIn(node) || startPass[node];
				if (isBuiltIn(node)) {
					earliest[node] = builtInPosition(node);
					continue;
				}
				int after = startPass[node] ? 0 : Integer.MIN_VALUE;
				for (int prev : predecessors.get(node)) {
					if (earliest[prev] != Integer.MIN_VALUE) {
						after = Math.max(after, isBuiltIn(prev) ? earliest[prev] + 1 : earliest[prev]);
					}
					anchored[node] |= anchored[prev] && !endPass[prev];
				}
				earliest[node] = after;
			}
			// built-in passes, START passes and passes following them: as early as possible
			for (int node : order) {
				if (isBuiltIn(node)) {
					place(node, earliest[node], LATE);
				} else if (startPass[node]) {
					place(node, earliest[node], START);
				} else if (anchored[node] && !endPass[node]) {
					place(node, earliest[node], EARLY);
				}
			}
			// END passes and passes preceding a placed pass: as late as possible
			for (int i = order.size() - 1; i >= 0; i--) {
				int node = order.get(i);
				if (placed[node]) {
					continue;
				}
				int before = endPass[node] ? endPosition : Integer.MAX_VALUE;
				for (int next : successors.get(node)) {
					if (placed[next]) {
						before = Math.min(before, isBuiltIn(next) ? position[next] - 1 : position[next]);
					}
				}
				if (before != Integer.MAX_VALUE) {
					place(node, Math.max(before, earliest[node]), endPass[node] ? END : LATE);
				}
			}
			// the rest: right after the passes they follow, unconstrained passes at the end
			for (int node : order) {
				if (placed[node]) {
					continue;
				}
				List<Integer> prevs = predecessors.get(node);
				if (prevs.isEmpty()) {
					place(node, endPosition, END);
				} else {
					int after = earliest[node];
					for (int prev : prevs) {
						after = Math.max(after, position[prev]);
					}
					place(node, after, EARLY);
				}
			}
		}

		private void place(int node, int pos, int placeKind) {
			position[node] = pos;
			kind[node] = placeKind;
			placed[node] = true;
		}

		private JadxRuntimeException cycleError(List<Integer> order) {
			boolean[] sorted = new boolean[total];
			for (int node : order) {
				sorted[node] = true;
			}
			List<String> customPasses = new ArrayList<>();
			// built-in passes on a cycle, as runs of consecutive pipeline passes (can be long)
			List<String> builtInRuns = new ArrayList<>();
			int runStart = -1;
			for (int node = 0; node <= total; node++) {
				boolean onCycle = node < total && !sorted[node] && reachesItself(node, sorted);
				if (onCycle && isBuiltIn(node)) {
					if (runStart == -1) {
						runStart = node;
					}
					continue;
				}
				if (runStart != -1) {
					int runEnd = node - 1;
					builtInRuns.add(runStart == runEnd ? names.get(runStart) : names.get(runStart) + " .. " + names.get(runEnd));
					runStart = -1;
				}
				if (onCycle) {
					JadxPassInfo info = info(node);
					customPasses.add(names.get(node)
							+ " (runAfter: " + info.runAfter() + ", runBefore: " + info.runBefore() + ')');
				}
			}
			String msg = "Conflict order requirements: cyclic dependencies between passes: " + customPasses;
			if (!builtInRuns.isEmpty()) {
				msg += " through built-in passes: " + builtInRuns;
			}
			return new JadxRuntimeException(msg);
		}

		private boolean reachesItself(int start, boolean[] sorted) {
			boolean[] visited = new boolean[total];
			Deque<Integer> stack = new ArrayDeque<>(successors.get(start));
			while (!stack.isEmpty()) {
				int node = stack.pop();
				if (node == start) {
					return true;
				}
				if (!sorted[node] && !visited[node]) {
					visited[node] = true;
					stack.addAll(successors.get(node));
				}
			}
			return false;
		}
	}
}
