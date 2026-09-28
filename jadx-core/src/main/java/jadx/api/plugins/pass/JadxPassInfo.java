package jadx.api.plugins.pass;

import java.util.List;

public interface JadxPassInfo {

	/**
	 * Add this as the only entry of 'run after' list to place pass before others.
	 * The pass still runs after passes that list it in their 'run before' list.
	 * Its own 'run before' list is honoured; unknown pass names there are ignored with a warning.
	 */
	String START = "start";

	/**
	 * Add this as the only entry of 'run before' list to place pass at end.
	 * The pass still runs before passes that list it in their 'run after' list.
	 * Its own 'run after' list is honoured; unknown pass names there are ignored with a warning.
	 */
	String END = "end";

	/**
	 * Pass short id, should be unique.
	 */
	String getName();

	/**
	 * Pass description
	 */
	String getDescription();

	/**
	 * This pass will be executed after these passes.
	 * Passes names list.
	 */
	List<String> runAfter();

	/**
	 * This pass will be executed before these passes.
	 * Passes names list.
	 */
	List<String> runBefore();
}
