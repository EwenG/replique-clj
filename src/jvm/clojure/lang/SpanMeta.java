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

import java.util.Iterator;

/**
 * The four-key source-position map the reader attaches to every symbol and
 * collection it reads while analysis is on ({@link LispReader#attachSourcePosition}).
 * It is exactly {@code {:line l :column c :end-line el :end-column ec}} - same keys,
 * same order, same Integer values - but holds the four coordinates as primitive
 * {@code int} fields, so creating one costs a single object instead of a
 * PersistentArrayMap plus an eight-slot backing array plus a boxed Integer per
 * coordinate whose value exceeds the Integer cache.
 *
 * <p>This is a REPRESENTATION, not a behaviour: it must be indistinguishable from the
 * PersistentArrayMap it stands in for, because consumers do ordinary map things to it
 * - {@code select-keys} it onto a Var's metadata, {@code dissoc} the position keys back
 * off it (clojure.cljs.reader/program-meta, and syntax-quote in LispReader), compare it,
 * merge it, seq it. So every operation beyond the cheap reads (count / valAt /
 * containsKey / entryAt) MATERIALISES the equivalent PersistentArrayMap and defers to
 * it, which keeps the semantics exact by construction rather than by re-derivation.
 * Those operations are rare next to creation, which is the one being optimised.
 *
 * <p>Extending APersistentMap is what makes that safe: equals, equiv, hashCode, hasheq,
 * cons and the java.util.Map surface all come from there and are defined in terms of
 * seq(), so a SpanMeta and the PersistentArrayMap it materialises to are = to each
 * other and hash alike.
 */
public class SpanMeta extends APersistentMap implements IObj, IKVReduce{

final IPersistentMap _meta;
final int line;
final int column;
final int endLine;
final int endColumn;

public SpanMeta(int line, int column, int endLine, int endColumn){
	this(null, line, column, endLine, endColumn);
}

SpanMeta(IPersistentMap meta, int line, int column, int endLine, int endColumn){
	this._meta = meta;
	this.line = line;
	this.column = column;
	this.endLine = endLine;
	this.endColumn = endColumn;
}

// The PersistentArrayMap this stands in for: same keys, same insertion order, same
// boxing. Everything structural defers to it.
private PersistentArrayMap materialize(){
	return new PersistentArrayMap(_meta, new Object[]{
			RT.LINE_KEY, line, RT.COLUMN_KEY, column,
			LispReader.END_LINE_KEY, endLine, LispReader.END_COLUMN_KEY, endColumn});
}

// 0..3 for the four position keys, -1 otherwise. Keywords are interned so identity
// normally settles it; the equals fallback keeps a deserialised or otherwise
// non-identical key working.
private static int idx(Object key){
	if(key == RT.LINE_KEY) return 0;
	if(key == RT.COLUMN_KEY) return 1;
	if(key == LispReader.END_LINE_KEY) return 2;
	if(key == LispReader.END_COLUMN_KEY) return 3;
	if(RT.LINE_KEY.equals(key)) return 0;
	if(RT.COLUMN_KEY.equals(key)) return 1;
	if(LispReader.END_LINE_KEY.equals(key)) return 2;
	if(LispReader.END_COLUMN_KEY.equals(key)) return 3;
	return -1;
}

private static Keyword keyAt(int i){
	switch(i)
		{
		case 0: return RT.LINE_KEY;
		case 1: return RT.COLUMN_KEY;
		case 2: return LispReader.END_LINE_KEY;
		default: return LispReader.END_COLUMN_KEY;
		}
}

private int intAt(int i){
	switch(i)
		{
		case 0: return line;
		case 1: return column;
		case 2: return endLine;
		default: return endColumn;
		}
}

public int count(){
	return 4;
}

public boolean containsKey(Object key){
	return idx(key) >= 0;
}

public IMapEntry entryAt(Object key){
	int i = idx(key);
	return i < 0 ? null : MapEntry.create(keyAt(i), intAt(i));
}

public Object valAt(Object key, Object notFound){
	int i = idx(key);
	return i < 0 ? notFound : Integer.valueOf(intAt(i));
}

public Object valAt(Object key){
	return valAt(key, null);
}

// Any assoc - even of a position key, whose new value need not be an int - yields an
// ordinary map, so the result is exactly what PersistentArrayMap would have produced.
public IPersistentMap assoc(Object key, Object val){
	return materialize().assoc(key, val);
}

public IPersistentMap assocEx(Object key, Object val){
	return materialize().assocEx(key, val);
}

// Absent key returns this unchanged, as PersistentArrayMap does; present key drops
// out of the materialised map. Both matter: program-meta dissocs all six positional
// keys (two of which, :file and :source, are never here) and expects an empty map.
public IPersistentMap without(Object key){
	return idx(key) < 0 ? this : materialize().without(key);
}

public ISeq seq(){
	return materialize().seq();
}

public Iterator iterator(){
	return materialize().iterator();
}

public IPersistentCollection empty(){
	return (IPersistentCollection) PersistentArrayMap.EMPTY.withMeta(_meta);
}

public Object kvreduce(IFn f, Object init){
	return materialize().kvreduce(f, init);
}

public IPersistentMap meta(){
	return _meta;
}

public SpanMeta withMeta(IPersistentMap meta){
	if(meta == _meta)
		return this;
	return new SpanMeta(meta, line, column, endLine, endColumn);
}

}
