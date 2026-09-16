/**
 *   Copyright (c) Rich Hickey. All rights reserved.
 *   The use and distribution terms for this software are covered by the
 *   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
 *   which can be found in the file epl-v10.html at the root of this distribution.
 *   By using this software in any fashion, you are agreeing to be bound by
 * 	 the terms of this license.
 *   You must not remove this notice, or any other, from this software.
 **/

package clojure.lang;

import java.util.concurrent.ConcurrentHashMap;

/**
 * A registry of namespaces - the symbol table one language's compilation runs
 * against. Namespaces were always just symbol tables; this only gives that table
 * an identity, so there can be more than one.
 *
 * {@link #DEFAULT} holds the JVM's namespaces and is what {@link Namespace#find},
 * {@link Namespace#findOrCreate}, {@link Namespace#remove}, {@link Namespace#all}
 * and clojure.core's find-ns / create-ns / remove-ns / all-ns address. That path is
 * unchanged: the vendored compiler never sees another world, and nothing here costs
 * it an indirection it did not already pay.
 *
 * Further worlds exist so a front end for another target can intern its own vars in
 * its own namespaces without colliding with the JVM's - the consumer is the sibling
 * project ../replique-cljs, whose doc/cljs-compiler.md is where the design lives -
 * a ClojureScript clojure.string and the JVM's clojure.string are different
 * namespaces holding different vars, and both must be able to exist at once.
 *
 * A Namespace does NOT know which world it belongs to. Every caller that resolves a
 * symbol already holds the world explicitly, so a back-pointer would only be a
 * second source of truth to keep in agreement with the first.
 */
public class NamespaceWorld {

/**
 * The JVM's namespaces. Everything in the vendored runtime addresses this one.
 */
final static public NamespaceWorld DEFAULT = new NamespaceWorld(null);

/**
 * Mappings a namespace created in this world starts with, or null for the host's
 * default imports (java.lang and friends, {@link RT#DEFAULT_IMPORTS}) - which is
 * what DEFAULT wants.
 *
 * Null rather than RT.DEFAULT_IMPORTS directly because DEFAULT is built during this
 * class's initialization, which RT's own initialization triggers (RT.CLOJURE_NS
 * calls Namespace.findOrCreate); reading an RT field there would make correctness
 * depend on field order inside RT. Namespace's constructor resolves it lazily, at
 * namespace-creation time, exactly as it did before.
 *
 * A target with no host classes - ClojureScript - passes an empty map instead.
 */
final IPersistentMap initialMappings;

final ConcurrentHashMap<Symbol, Namespace> namespaces = new ConcurrentHashMap<Symbol, Namespace>();

public NamespaceWorld(IPersistentMap initialMappings){
	this.initialMappings = initialMappings;
}

/**
 * A world whose namespaces start empty - no host imports.
 */
public NamespaceWorld(){
	this(RT.map());
}

public Namespace find(Symbol name){
	return namespaces.get(name);
}

public Namespace findOrCreate(Symbol name){
	Namespace ns = namespaces.get(name);
	if(ns != null)
		return ns;
	Namespace newns = new Namespace(name, initialMappings);
	ns = namespaces.putIfAbsent(name, newns);
	return ns == null ? newns : ns;
}

public Namespace remove(Symbol name){
	return namespaces.remove(name);
}

public ISeq all(){
	return RT.seq(namespaces.values());
}
}
