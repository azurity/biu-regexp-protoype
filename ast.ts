const iconv = require('iconv-lite');
import { ucd } from "./unicode";


export const FlagDefault = 0;
export const FlagIgnoreICase = 1;
export const FlagMultiline = 2;

export class MatchResult {
    result: string = '';
    position: number = 0;
}

export type MatchResultSet = Map<number | string, MatchResult>;

interface MatchInternal {
    result: MatchResultSet;
    index: number;
}

export interface Context {
    direct: number; // 1/-1
    flag: number;
}

export interface State {
    value: null | DisjunctionState | AlternativeState | WithQuantifierState | NthState
}

interface DisjunctionState {
    branch: number;
    sub: State;
}

interface AlternativeState {
    sub: State[];
    tempResult: (MatchInternal | null)[];
}

interface WithQuantifierState {
    minN: number;
    maxN: number;
    sub: State[];
    tempResult: (MatchInternal | null)[];
}

interface NthState {
    n: number;
}



type CodePoint = number;

class Quantifier {
    min: number = 0;
    max: number = 0;
    less: boolean = false;

    toString() {
        return `{${this.min},${this.max < 0 ? '' : this.max}${this.less ? '?' : ''}}`
    }
}

export class RegAST {
    type: string = '';

    toString(): string {
        return '';
    }
    toTree(prefix: string): string {
        return this.toString();
    }
    match(data: Uint32Array, index: number, state: State, context: Context): MatchInternal | null {
        return null;
    }
    allocCapture(index: number) {
        return index;
    }
}

class Disjunction extends RegAST {
    type: 'disjunction' = 'disjunction';
    body: Alternative[] = [];

    toString() {
        return this.body.map(it => it.toString()).join('|');
    }
    toTree(prefix: string): string {
        return this.body.map(it => it.toTree(prefix)).join(`\n${prefix}|\n${prefix}`);
    }
    allocCapture(index: number) {
        for (let it of this.body) {
            index = it.allocCapture(index);
        }
        return index;
    }
    match(data: Uint32Array, index: number, state: State, context: Context): MatchInternal | null {
        if (state.value === null) {
            // init state
            state.value = {
                branch: 0,
                sub: { value: null },
            } as DisjunctionState;
        }
        let cased = state.value as DisjunctionState;
        if (cased.branch == 0 && this.body.length == 0) {
            return {
                result: new Map(),
                index: index,
            };
        }
        if (cased.branch >= this.body.length) {
            return null;
        }
        while (cased.branch < this.body.length) {
            let ret = this.body[cased.branch].match(data, index, cased.sub, context);
            if (ret == null) {
                cased.branch += 1;
                cased.sub = { value: null };
            } else {
                return ret;
            }
        }
        return null;
    }
}

class Alternative extends RegAST {
    type: 'alternative' = 'alternative';
    body: (Atom | WithQuantifier)[] = [];

    toString() {
        return this.body.map(it => it.toString()).join('');
    }
    toTree(prefix: string) {
        return this.body.map(it => it.toTree(prefix)).join('');
    }
    allocCapture(index: number) {
        for (let it of this.body) {
            index = it.allocCapture(index);
        }
        return index;
    }
    match(data: Uint32Array, index: number, state: State, context: Context): MatchInternal | null {
        let cur = this.body.length - 1;
        if (context.direct < 0) {
            cur = 0;
        }
        if (state.value === null) {
            // init state
            let sub = [];
            let tr = [];
            for (let i = 0; i < this.body.length; i++) {
                sub.push({ value: null } as State);
                tr.push(null);
            }
            state.value = {
                sub: sub,
                tempResult: tr,
            } as AlternativeState;
            if (context.direct > 0) {
                cur = 0;
            } else {
                cur = this.body.length - 1;
            }
        }
        let cased = state.value as AlternativeState;
        let i = index;
        if (context.direct > 0 && cur > 0) {
            i = cased.tempResult[cur - 1]!.index;
        } else if (context.direct < 0 && cur < this.body.length - 1) {
            i = cased.tempResult[cur + 1]!.index;
        }
        while (cur >= 0 && cur < this.body.length) {
            let ret = this.body[cur].match(data, i, cased.sub[cur], context);
            if (ret == null) {
                cased.sub[cur].value = null;
                cased.tempResult[cur] = null;
                cur -= context.direct;
            } else {
                cased.tempResult[cur] = ret;
                i = ret.index;
                cur += context.direct;
            }
            if ((context.direct > 0 && cur == this.body.length) || (context.direct < 0 && cur == -1)) {
                let result: MatchResultSet = new Map();
                for (let set of cased.tempResult) {
                    for (let it of set!.result) {
                        result.set(...it);
                    }
                }
                return {
                    result: result,
                    index: i,
                };
            }
        }
        return null;
    }
}

class WithQuantifier extends RegAST {
    atom?: Atom;
    quantifier?: Quantifier;

    toString() {
        return this.atom!.toString() + this.quantifier!.toString();
    }
    toTree(prefix: string): string {
        return `${this.atom!.toTree(prefix)}${this.quantifier}`;
    }
    allocCapture(index: number) {
        return this.atom!.allocCapture(index);
    }
    match(data: Uint32Array, index: number, state: State, context: Context): MatchInternal | null {
        if (state.value === null) {
            // init state
            state.value = {
                minN: this.quantifier!.min,
                maxN: this.quantifier!.max,
                sub: [],
                tempResult: [],
            } as WithQuantifierState;
        }
        let cased = state.value as WithQuantifierState;
        if (this.quantifier!.less) {
            while (cased.minN <= cased.maxN || cased.maxN < 0) {
                let limit = cased.minN;
                let i = index;
                if (cased.tempResult.length > 0) {
                    i = cased.tempResult[cased.tempResult.length - 1]!.index;
                }
                let cur = cased.tempResult.length - 1;
                if (cur < 0) { cur = 0; }
                while (cur >= 0) {
                    if (cased.sub.length == cur) {
                        cased.sub.push({ value: null });
                        cased.tempResult.push(null);
                    }
                    let ret = this.atom!.match(data, i, cased.sub[cur], context);
                    if (ret == null) {
                        cased.sub.pop();
                        cased.tempResult.pop();
                        cur -= 1;
                    } else {
                        cased.tempResult[cur] = ret;
                        i = ret.index;
                        cur += 1;
                    }
                    if (cur == limit) {
                        let result: MatchResultSet = new Map();
                        for (let set of cased.tempResult) {
                            for (let it of set!.result) {
                                result.set(...it);
                            }
                        }
                        return {
                            result: result,
                            index: i,
                        };
                    }
                }
                cased.minN += 1;
            }
            return null;
        } else {
            while (cased.minN <= cased.maxN || cased.maxN < 0) {
                let limit = cased.maxN;
                let i = index;
                if (cased.tempResult.length > 0) {
                    i = cased.tempResult[cased.tempResult.length - 1]!.index;
                }
                let cur = cased.tempResult.length - 1;
                if (cur < 0) { cur = 0; }
                let d = 0;
                while (cur >= 0) {
                    if (cased.sub.length == cur) {
                        cased.sub.push({ value: null });
                        cased.tempResult.push(null);
                    }
                    let finish = false;
                    let ret = this.atom!.match(data, i, cased.sub[cur], context);
                    if (ret == null) {
                        cased.sub.pop();
                        cased.tempResult.pop();
                        cur -= 1;
                        if (limit <= 0) {
                            if (d >= 0 && (cur + 1) >= cased.minN) {
                                finish = true;
                            }
                        }
                        d = -1;
                    } else {
                        cased.tempResult[cur] = ret;
                        i = ret.index;
                        cur += 1;
                        d = 1;
                    }
                    if (cur >= 0 && cur == limit) {
                        finish = true;
                    }
                    if (finish) {
                        let result: MatchResultSet = new Map();
                        for (let set of cased.tempResult) {
                            for (let it of set!.result) {
                                result.set(...it);
                            }
                        }
                        if (limit < 0) {
                            let newL = -cased.tempResult.length - 1;
                            if (newL < limit) {
                                cased.maxN = newL;
                            }
                        }
                        return {
                            result: result,
                            index: i,
                        };
                    }
                }
                if (cased.maxN < 0) {
                    cased.maxN = -cased.maxN - 1;
                }
                cased.maxN -= 1;
                if (cased.maxN < 0) {
                    return null;
                }
            }
            return null;
        }
    }
}

// \b \B
class WordAssertNode extends RegAST {
    type: 'word-assert' = 'word-assert';
    without: boolean = false;

    toString() {
        return this.without ? '\\B' : '\\b';
    }
    match(data: Uint32Array, index: number, state: State, context: Context): MatchInternal | null {
        if (state.value === null) {
            // init state
            state.value = {
                n: 0,
            } as NthState;
        }
        let cased = state.value as NthState;
        if (cased.n > 0) return null;
        if (index < 0 || index >= data.length) {
            cased.n += 1;
            return {
                result: new Map(),
                index: index,
            };
        }
        let matched = charIsWord(data[index]) !== charIsWord(data[index - context.direct]);
        if (matched !== this.without) {
            cased.n += 1;
            return {
                result: new Map(),
                index: index,
            };
        } else {
            return null;
        }
    }
}

// (?=), (?!)
class LookAroundNode extends RegAST {
    type: 'look-around' = 'look-around';
    without: boolean = false;
    body?: Disjunction;

    toString() {
        return `(?${this.without ? '!' : '='}${this.body})`;
    }
    toTree(prefix: string) {
        return `(?${this.without ? '!' : '='}\n${prefix + '  '}${this.body!.toTree(prefix + '  ')}\n${prefix})`;
    }

    match(data: Uint32Array, index: number, state: State, context: Context): MatchInternal | null {
        if (state.value === null) {
            // init state
            state.value = {
                n: 0,
            } as NthState;
        }
        let cased = state.value as NthState;
        if (cased.n > 0) return null;
        let oldDirect = context.direct;
        context.direct = 1;
        let toggle = oldDirect < 0 ? 1 : 0;
        let ret = this.body!.match(data, index + toggle, { value: null }, context);
        context.direct = oldDirect;
        if (ret == null) {
            return null;
        }
        cased.n += 1;
        return {
            result: new Map(),
            index: index,
        };
    }
}

// (?<=), (?<!)
class BackReferenceNode extends RegAST {
    type: 'back-reference' = 'back-reference';
    without: boolean = false;
    body?: Disjunction;

    toString() {
        return `(?<${this.without ? '!' : '='}${this.body})`;
    }
    toTree(prefix: string) {
        return `(?<${this.without ? '!' : '='}\n${prefix + '  '}${this.body!.toTree(prefix + '  ')}\n${prefix})`;
    }
    match(data: Uint32Array, index: number, state: State, context: Context): MatchInternal | null {
        if (state.value === null) {
            // init state
            state.value = {
                n: 0,
            } as NthState;
        }
        let cased = state.value as NthState;
        if (cased.n > 0) return null;
        let oldDirect = context.direct;
        context.direct = -1;
        let toggle = oldDirect > 0 ? 1 : 0;
        let ret = this.body!.match(data, index - toggle, { value: null }, context);
        context.direct = oldDirect;
        if (ret == null) {
            return null;
        }
        cased.n += 1;
        return {
            result: new Map(),
            index: index,
        };
    }
}

const LineTerminatorSet = new Set('\r\n\u2028\u2029');
function charIsLineTerminator(char: number) {
    return LineTerminatorSet.has(String.fromCodePoint(char));
}

// ^
class BeginAssertNode extends RegAST {
    type: 'begin-assert' = 'begin-assert';

    toString() {
        return '^';
    }
    match(data: Uint32Array, index: number, state: State, context: Context): MatchInternal | null {
        if (state.value === null) {
            // init state
            state.value = {
                n: 0,
            } as NthState;
        }
        let cased = state.value as NthState;
        if (cased.n > 0) return null;
        if (index != 0) {
            if ((context.flag & FlagMultiline) == 0) {
                return null;
            } else {
                if (!charIsLineTerminator(data[index - 1])) {
                    return null;
                }
            }
        }
        cased.n += 1;
        return {
            result: new Map(),
            index: index,
        };
    }
}

// $
class EndAssertNode extends RegAST {
    type: 'end-assert' = 'end-assert';

    toString() {
        return '$';
    }
    match(data: Uint32Array, index: number, state: State, context: Context): MatchInternal | null {
        if (state.value === null) {
            // init state
            state.value = {
                n: 0,
            } as NthState;
        }
        let cased = state.value as NthState;
        if (cased.n > 0) return null;
        if (index == data.length) {
            cased.n += 1;
            return {
                result: new Map(),
                index: index,
            };
        } else {
            if (((context.flag & FlagMultiline) != 0) && (charIsLineTerminator(data[index]))) {
                return {
                    result: new Map(),
                    index: index,
                };
            }
        }
        return null;
    }
}

// .
class DotNode extends RegAST {
    type: 'dot' = 'dot';

    toString() {
        return '.';
    }
    match(data: Uint32Array, index: number, state: State, context: Context): MatchInternal | null {
        if (state.value === null) {
            // init state
            state.value = {
                n: 0,
            } as NthState;
        }
        let cased = state.value as NthState;
        if (cased.n > 0) return null;
        if (index < 0 || index >= data.length) {
            return null;
        }
        if (((context.flag & FlagMultiline) != 0) && (charIsLineTerminator(data[index] - 1))) {
            return null;
        }
        cased.n += 1;
        return {
            result: new Map(),
            index: index + context.direct,
        };
    }
}

function CodePointToString(c: CodePoint) {
    let s = JSON.stringify(String.fromCharCode(c));
    return s.slice(1, s.length - 1);
}

class CharNode extends RegAST {
    type: 'char' = 'char';
    char: CodePoint = -1;

    toString() {
        return CodePointToString(this.char);
    }
    match(data: Uint32Array, index: number, state: State, context: Context): MatchInternal | null {
        if (state.value === null) {
            // init state
            state.value = {
                n: 0,
            } as NthState;
        }
        let cased = state.value as NthState;
        if (cased.n > 0) return null;
        if (index < 0 || index >= data.length) {
            return null;
        }
        if ((context.flag & FlagIgnoreICase) == 0) {
            if (data[index] != this.char) {
                return null;
            }
        } else {
            let left = ucd.getUpper(data[index]) ?? data[index];
            let right = ucd.getUpper(this.char) ?? data[index];
            if (left != right) {
                return null;
            }
        }
        cased.n += 1;
        return {
            result: new Map(),
            index: index + context.direct,
        };
    }
}

class DecimalEscapeNode extends RegAST {
    type: 'decimal' = 'decimal';
    value: number = 0;

    toString() {
        return `\\${this.value}`;
    }
    match(data: Uint32Array, index: number, state: State, context: Context): MatchInternal | null {
        return null;
    }
}

interface Prop {
    name: string;
    value: string;
};

function charIsWord(char: number): boolean {
    return (char >= '0'.codePointAt(0)! && char <= '9'.codePointAt(0)!) ||
        (char >= 'a'.codePointAt(0)! && char <= 'z'.codePointAt(0)!) ||
        (char >= 'A'.codePointAt(0)! && char <= 'Z'.codePointAt(0)!) ||
        (char == '_'.codePointAt(0));
}

class ClassNode extends RegAST {
    type: 'class' = 'class';
    prop: 'd' | 'D' | 's' | 'S' | 'w' | 'W' | 'p' | 'P' | null = null;
    value?: Prop;

    toString() {
        if (this.prop == 'p' || this.prop == 'P') {
            return `\\${this.prop}{?${this.value!.name}=${this.value!.value}}`;
        } else {
            return `\\${this.prop}`;
        }
    }
    match(data: Uint32Array, index: number, state: State, context: Context): MatchInternal | null {
        if (state.value === null) {
            // init state
            state.value = {
                n: 0,
            } as NthState;
        }
        let cased = state.value as NthState;
        if (cased.n > 0) return null;
        if (index < 0 || index >= data.length) {
            return null;
        }
        if (this.prop!.toLowerCase() == 'p') {
            let result: boolean | null = null;
            if (ucd._propNameAlias.get(this.value!.name) == 'gc') {
                result = ucd.getGeneralCategoryProp(data[index]).name == this.value!.value;
            } else if (ucd._propNameAlias.get(this.value!.name) == 'sc') {
                result = ucd.getScriptProp(data[index]).name == this.value!.value;
            }
            if (result === (this.prop!.toLowerCase() == 'p')) {
                cased.n += 1;
                return {
                    result: new Map(),
                    index: index + context.direct,
                };
            } else {
                return null;
            }
        } else if (this.prop!.toLowerCase() == 'd') {
            let result = data[index] >= '0'.codePointAt(0)! && data[index] <= '9'.codePointAt(0)!;
            if (result === (this.prop!.toLowerCase() == 'd')) {
                cased.n += 1;
                return {
                    result: new Map(),
                    index: index + context.direct,
                };
            } else {
                return null;
            }
        } else if (this.prop!.toLowerCase() == 'w') {
            let result = charIsWord(data[index]);
            if (result === (this.prop!.toLowerCase() == 'w')) {
                cased.n += 1;
                return {
                    result: new Map(),
                    index: index + context.direct,
                };
            } else {
                return null;
            }
        } else if (this.prop!.toLowerCase() == 's') {
            let sp = new Set('\x09\x0A\x0B\x0C\x0D\x20\x85\xA0\u1680\u2000\u2001\u2002\u2003\u2004\u2005\u2006\u2007\u2008\u2009\u200A\u2028\u2029\u202f\u205f\u3000')
            let result = sp.has(String.fromCodePoint(data[index]));
            if (result === (this.prop!.toLowerCase() == 's')) {
                cased.n += 1;
                return {
                    result: new Map(),
                    index: index + context.direct,
                };
            } else {
                return null;
            }
        } else {
            return null;
        }
    }
}

class RefGroupNode extends RegAST {
    type: 'reg-group' = 'reg-group';
    value: string = '';

    toString() {
        return `\\k<${this.value}>`;
    }
    match(data: Uint32Array, index: number, state: State, context: Context): MatchInternal | null {
        return null;
    }
}

// (), (?:)
class GroupNode extends RegAST {
    type: 'group' = 'group';
    body?: Disjunction;
    capture: number | null = -1;
    captureName: string | null = null;

    toString() {
        if (this.capture === null) {
            return `(?:${this.body})`;
        } else if (this.captureName !== null) {
            return `(?<${this.capture}>${this.body})`;
        } else {
            return `(${this.body})`;
        }
    }
    toTree(prefix: string) {
        if (this.capture === null) {
            return `(?:\n${prefix + '  '}${this.body!.toTree(prefix + '  ')}\n${prefix})`;
        } else if (this.captureName !== null) {
            return `(?<${this.capture}>\n${prefix + '  '}${this.body!.toTree(prefix + '  ')}\n${prefix})`;
        } else {
            return `(\n${prefix + '  '}${this.body!.toTree(prefix + '  ')}\n${prefix})`;
        }
    }
    allocCapture(index: number) {
        this.capture = index;
        return this.body!.allocCapture(index + 1);
    }
    match(data: Uint32Array, index: number, state: State, context: Context): MatchInternal | null {
        let ret = this.body!.match(data, index, state, context);
        if (ret == null) {
            return null;
        }
        if (this.capture !== null) {
            ret.result.set(this.capture, {
                result: iconv.decode(Buffer.from(data.slice(index, ret.index).buffer), 'UTF-32'),
                position: index,
            });
        }
        if (this.captureName !== null) {
            ret.result.set(this.captureName, {
                result: iconv.decode(Buffer.from(data.slice(index, ret.index).buffer), 'UTF-32'),
                position: index,
            });
        }
        return {
            result: ret.result,
            index: ret.index,
        }
    }
}

// *-*
class RangeNode extends RegAST {
    type: 'range' = 'range';
    begin: CodePoint = -1;
    end: CodePoint = -1;

    toString() {
        return `${CodePointToString(this.begin)}-${CodePointToString(this.end)}`;
    }
    match(data: Uint32Array, index: number, state: State, context: Context): MatchInternal | null {
        if (index >= data.length) {
            return null;
        }
        if (data[index] >= this.begin && data[index] <= this.end) {
            return {
                result: new Map(),
                index: index + context.direct,
            };
        }
        return null;
    }
}

// [ * ]
class CharacterClassNode extends RegAST {
    type: 'character-class' = 'character-class';
    without: boolean = false;
    body: (RangeNode | ClassNode | CharNode)[] = [];

    toString() {
        return `[${this.without ? '^' : ''}${this.body.map(it => it.toString()).join('')}]`;
    }
    toTree(prefix: string) {
        return `[${this.without ? '^' : ''}\n${prefix + '  '}${this.body.map(it => it.toTree(prefix)).join(`\n${prefix + '  '}`)}\n${prefix}]`;
    }
    match(data: Uint32Array, index: number, state: State, context: Context): MatchInternal | null {
        if (state.value === null) {
            // init state
            state.value = {
                n: 0,
            } as NthState;
        }
        let cased = state.value as NthState;
        if (cased.n > 0) return null;
        for (let it of this.body) {
            let ret = it.match(data, index, { value: null }, context);
            if (ret != null) {
                cased.n += 1;
                return ret;
            }
        }
        return null;
    }
}

type Atom = DotNode | CharacterClassNode | GroupNode | DecimalEscapeNode | ClassNode | RefGroupNode | CharNode;

export function ParsePattern(data: Uint32Array): Disjunction | null {
    let ret = ParseDisjunction(data, 0);
    if (ret == null) {
        return null;
    }
    return ret.result;
}

function ParseDisjunction(data: Uint32Array, index: number): { result: Disjunction, index: number } | null {
    let items = [];
    let i = index;
    while (i < data.length) {
        let ret = ParseAlternative(data, i);
        if (ret == null) {
            return null;
        }
        items.push(ret.result);
        i = ret.index;
        if (i >= data.length) {
            break;
        }
        if (data[i] == '|'.codePointAt(0)) {
            i += 1;
        } else if (data[i] == ')'.codePointAt(0)) {
            break;
        } else {
            return null;
        }
    }
    let ret = new Disjunction();
    ret.body = items;
    return {
        result: ret,
        index: i,
    }
}

const TermMatcher = [ParseAssertion, ParseAtom];
function ParseAlternative(data: Uint32Array, index: number): { result: Alternative, index: number } | null {
    let items = [];
    let i = index;
    while (i < data.length) {
        let matched = false;
        for (let matcher of TermMatcher) {
            let ret = matcher(data, i);
            if (ret != null) {
                items.push(ret.result);
                i = ret.index;
                matched = true;
                break;
            }
        }
        if (!matched) {
            break;
        }
    }
    let ret = new Alternative();
    ret.body = items;
    return {
        result: ret,
        index: i,
    }
}

type Assertion = BeginAssertNode | EndAssertNode | WordAssertNode | BackReferenceNode | LookAroundNode;
function ParseAssertion(data: Uint32Array, index: number): { result: Assertion, index: number } | null {
    if (index >= data.length) {
        return null;
    }
    if (data[index] == '^'.codePointAt(0)) {
        return {
            result: new BeginAssertNode(),
            index: index + 1,
        }
    } else if (data[index] == '$'.codePointAt(0)) {
        return {
            result: new EndAssertNode(),
            index: index + 1,
        }
    } else if (data[index] == '\\'.codePointAt(0)) {
        let ret = new WordAssertNode();
        if (data[index + 1] == 'b'.codePointAt(0)) {
            ret.without = false;
        } else if (data[index + 1] == 'b'.codePointAt(0)) {
            ret.without = true;
        } else {
            return null;
        }
        return {
            result: ret,
            index: index + 2,
        };
    } else {
        if (index + 4 > data.length) {
            return null;
        }
        if (data[index] != '('.codePointAt(0) || data[index + 1] != '?'.codePointAt(0)) {
            return null;
        }
        let pre = false;
        let cur = index + 2;
        if (data[index + 2] == '<'.codePointAt(0)) {
            if (index + 5 > data.length) {
                return null;
            }
            pre = true;
            cur += 1;
        }
        let withNot = false;
        if (data[cur] == '='.codePointAt(0)) {
            withNot = false;
        } else if (data[cur] == '!'.codePointAt(0)) {
            withNot = true;
        } else {
            return null;
        }
        let ret = ParseDisjunction(data, cur + 1);
        if (ret == null) {
            return null;
        }
        if (data[ret.index] != ')'.codePointAt(0)) {
            return null;
        }
        if (pre) {
            let result = new BackReferenceNode();
            result.body = ret.result;
            result.without = withNot;
            return {
                result: result,
                index: ret.index + 1,
            };
        } else {
            let result = new LookAroundNode();
            result.body = ret.result;
            result.without = withNot;
            return {
                result: result,
                index: ret.index + 1,
            };
        }
    }
}

function ParseAtom(data: Uint32Array, index: number): { result: Atom | WithQuantifier, index: number } | null {
    let ret = ParseAtomBody(data, index);
    if (ret == null) {
        return ret;
    }
    let qret = ParseQuantifier(data, ret.index);
    if (qret == null) {
        return ret;
    }
    let result = new WithQuantifier();
    result.atom = ret.result;
    result.quantifier = qret.result;
    return {
        result: result,
        index: qret.index,
    };
}

function ParseQuantifier(data: Uint32Array, index: number): { result: Quantifier, index: number } | null {
    let ret = new Quantifier();
    let i = index;
    if (i >= data.length) {
        return null;
    }
    if (data[index] == '*'.codePointAt(0)) {
        ret.min = 0;
        ret.max = -1;
        i = i + 1;
    } else if (data[index] == '+'.codePointAt(0)) {
        ret.min = 1;
        ret.max = -1;
        i = i + 1;
    } else if (data[index] == '?'.codePointAt(0)) {
        ret.min = 0;
        ret.max = 1;
        i = i + 1;
    } else if (data[index] == '{'.codePointAt(0)) {
        let nret = ParseNumber(data, i + 1);
        i = nret.index;
        ret.min = nret.result;
        ret.max = nret.result;
        if (i >= data.length) {
            return null;
        }
        if (data[i] == '}'.codePointAt(0)) {
            i = i + 1;
        } else {
            if (data[i] == ','.codePointAt(0)) {
                ret.max = -1;
                i = i + 1;
            } else {
                return null;
            }
            let nret = ParseNumber(data, i);
            if (nret != null) {
                ret.max = nret.result;
                i = nret.index;
            }
            if (i >= data.length) {
                return null;
            }
            if (data[i] == '}'.codePointAt(0)) {
                i = i + 1;
            } else {
                return null;
            }
        }
    } else {
        return null;
    }
    if (i < data.length && data[i] == '?'.codePointAt(0)) {
        ret.less = true;
        return {
            result: ret,
            index: i + 1,
        };
    } else {
        return {
            result: ret,
            index: i,
        };
    }
}

function ParseNumber(data: Uint32Array, index: number): { result: number, index: number } {
    let ret = 0;
    let i = index;
    while ((i < data.length) && (data[i]! >= '0'.codePointAt(0)!) && (data[i]! <= '9'.codePointAt(0)!)) {
        ret = ret * 10 + (data[i] - '0'.codePointAt(0)!);
        i = i + 1;
    }
    return {
        result: ret,
        index: i,
    };
}

const specialChar = "^$\.*+?()[]{}|";
// FIXME: current not support group ref
const AtomEscapeMatcher = [/*ParseDecimalEscape, */ParseCharacterClassEscape, /*ParseGroupNameEscape, */ParseCharacterEscape];
function ParseAtomBody(data: Uint32Array, index: number): { result: Atom, index: number } | null {
    if (index >= data.length) {
        return null;
    }
    if (data[index] == '.'.codePointAt(0)) {
        return {
            result: new DotNode(),
            index: index + 1,
        }
    } else if (data[index] == '\\'.codePointAt(0)) {
        for (let matcher of AtomEscapeMatcher) {
            let ret = matcher(data, index + 1);
            if (ret != null) {
                return ret;
            }
        }
        return null;
    } else if (data[index] == '['.codePointAt(0)) {
        return ParseCharacterClass(data, index + 1);
    } else if (data[index] == '('.codePointAt(0)) {
        return ParseGroup(data, index + 1);
    } else {
        for (let c of specialChar) {
            if (data[index] == c.codePointAt(0)) {
                return null;
            }
        }
        let ret = new CharNode();
        ret.char = data[index];
        return {
            result: ret,
            index: index + 1,
        }
    }
}

function ParseDecimalEscape(data: Uint32Array, index: number): { result: DecimalEscapeNode, index: number } | null {
    let ret = ParseNumber(data, index);
    if (index == ret.index) {
        return null;
    }
    let reuslt = new DecimalEscapeNode();
    reuslt.value = ret.result;
    return {
        result: reuslt,
        index: ret.index,
    }
}

const CommonCharacterClassChar = "dDsSwW";
function ParseCharacterClassEscape(data: Uint32Array, index: number): { result: ClassNode, index: number } | null {
    if (index >= data.length) {
        return null;
    }
    for (let c of CommonCharacterClassChar) {
        if (data[index] == c.codePointAt(0)) {
            let ret = new ClassNode();
            ret.prop = c as any;
            return {
                result: ret,
                index: index + 1,
            };
        }
    }
    if (data[index] == 'p'.codePointAt(0) || data[index] == 'P'.codePointAt(0)) {
        let prop = String.fromCodePoint(data[index]);
        let pret = ParsePropBody(data, index + 1);
        if (pret == null) {
            return null;
        }
        let ret = new ClassNode();
        ret.prop = prop as any;
        ret.value = pret.result;
        return {
            result: ret,
            index: pret.index,
        };
    }
    return null;
}

function ParsePropBody(data: Uint32Array, index: number): { result: Prop, index: number } | null {
    let i = index;
    let step = 0;
    let name = 'gc'; // default name is gc
    let value = '';
    while (i < data.length) {
        if (step == 0) {
            if (data[i] != '<'.codePointAt(0)) {
                return null;
            }
            step = 1;
        } else if (step == 1) {
            if (data[i] == '>'.codePointAt(0)) {
                step = 3;
                continue;
            } else if (data[i] == '='.codePointAt(0)) {
                name = value;
                step = 2;
            } else {
                value += String.fromCodePoint(data[i]);
            }
        } else if (step == 2) {
            if (data[i] == '>'.codePointAt(0)) {
                step = 3;
                continue;
            } else {
                value += String.fromCodePoint(data[i]);
            }
        } else {
            if (value.length == 0) {
                return null;
            }
            return {
                result: {
                    name: name,
                    value: value,
                },
                index: i + 1,
            }
        }
        i += 1;
    }
    return null;
}

const ControlLetterMap = new Map([
    ['f', '\f'],
    ['n', '\n'],
    ['r', '\r'],
    ['t', '\t'],
    ['v', '\v'],
    ['0', '\0'],
    ['e', '\x1B'], // FIXME: the escape escape is not standard!!!
]);
const HexSet = new Set('0123456789abcdefABCDEF');
function ParseCharacterEscape(data: Uint32Array, index: number): { result: CharNode, index: number } | null {
    if (index >= data.length) {
        return null;
    }
    if (ControlLetterMap.has(String.fromCodePoint(data[index]))) {
        let ret = new CharNode();
        ret.char = ControlLetterMap.get(String.fromCodePoint(data[index]))!.codePointAt(0)!;
        return {
            result: ret,
            index: index + 1,
        };
    }
    if (data[index] == 'c'.codePointAt(0)) {
        if (index + 1 < data.length) {
            if (data[index + 1] >= 'A'.codePointAt(0)! && data[index] <= 'Z'.codePointAt(0)!) {
                let ret = new CharNode();
                ret.char = data[index + 1] - 'A'.codePointAt(0)! + 1;
                return {
                    result: ret,
                    index: index + 2,
                };
            }
        }
    } else if (data[index] == 'x'.codePointAt(0)) {
        if (index + 2 < data.length) {
            let high = String.fromCodePoint(data[index + 1]);
            let low = String.fromCodePoint(data[index + 2]);
            if (HexSet.has(high) && HexSet.has(low)) {
                let ret = new CharNode();
                ret.char = parseInt((high + low).toUpperCase(), 16);
                return {
                    result: ret,
                    index: index + 3,
                };
            }
        }
    } else if (data[index] == 'u'.codePointAt(0)) {
        if (index + 4 < data.length) {
            let b0 = String.fromCodePoint(data[index + 1]);
            let b1 = String.fromCodePoint(data[index + 2]);
            let b2 = String.fromCodePoint(data[index + 3]);
            let b3 = String.fromCodePoint(data[index + 4]);
            if (HexSet.has(b0) && HexSet.has(b1) && HexSet.has(b2) && HexSet.has(b3)) {
                let ret = new CharNode();
                ret.char = parseInt((b0 + b1 + b2 + b3).toUpperCase(), 16);
                return {
                    result: ret,
                    index: index + 5,
                };
            }
        } else {
            let uret = ParseUnicode(data, index + 1);
            if (uret != null) {
                let ret = new CharNode();
                ret.char = uret.result;
                return {
                    result: ret,
                    index: uret.index,
                };
            }
        }
    }
    // fallback all
    let ret = new CharNode();
    ret.char = data[index];
    return {
        result: ret,
        index: index + 1,
    };
}

function ParseUnicode(data: Uint32Array, index: number): { result: number, index: number } | null {
    let i = index;
    let step = 0;
    let name = '';
    while (i < data.length) {
        if (step == 0) {
            if (data[i] != '{'.codePointAt(0)) {
                return null;
            }
            step = 1;
        } else if (step == 1) {
            if (data[i] == '}'.codePointAt(0)) {
                if (name.length == 0) {
                    return null;
                }
                let value = parseInt(name, 16);
                // TODO: ensurce name is meaningful unicode
                return {
                    result: value,
                    index: i + 1,
                }
            } else {
                let c = String.fromCodePoint(data[i]);
                if (!HexSet.has(c)) {
                    return null;
                }
                name += String.fromCodePoint(data[i]);
            }
        }
        i += 1;
    }
    return null;
}

function ParseGroupNameEscape(data: Uint32Array, index: number): { result: RefGroupNode, index: number } | null {
    if (index >= data.length) {
        return null;
    }
    if (data[index] != 'k'.codePointAt(0)) {
        return null;
    }
    let nret = ParseGroupName(data, index + 1);
    if (nret == null) {
        return null;
    }
    let ret = new RefGroupNode();
    ret.value = nret.result;
    return {
        result: ret,
        index: nret.index,
    };
}

function ParseGroupName(data: Uint32Array, index: number): { result: string, index: number } | null {
    let i = index;
    let step = 0;
    let name = '';
    while (i < data.length) {
        if (step == 0) {
            if (data[i] != '<'.codePointAt(0)) {
                return null;
            }
            step = 1;
        } else if (step == 1) {
            if (data[i] == '>'.codePointAt(0)) {
                if (name.length == 0) {
                    return null;
                }
                if (name == '') {
                    return null;
                }
                return {
                    result: name,
                    index: i + 1,
                }
            } else {
                name += String.fromCodePoint(data[i]);
            }
        }
        i += 1;
    }
    return null;
}

function ParseGroup(data: Uint32Array, index: number): { result: GroupNode, index: number } | null {
    let i = index;
    let step = 0;
    let capture: number | null = -1;
    let captureName: string | null = null;
    let body: Disjunction | undefined = undefined;
    while (i < data.length) {
        if (step == 0) {
            if (data[i] == '?'.codePointAt(0)) {
                i += 1;
                step = 1;
            } else {
                step = 2;
            }
        } else if (step == 1) {
            if (data[i] == ':'.codePointAt(0)) {
                capture = null;
                i += 1;
                step = 2;
            } else {
                let nret = ParseGroupName(data, i);
                if (nret != null) {
                    captureName = nret.result;
                    i = nret.index;
                } else {
                    return null;
                }
                step = 2;
            }
        } else if (step == 2) {
            let dret = ParseDisjunction(data, i);
            if (dret == null) {
                return null;
            }
            body = dret.result;
            i = dret.index;
            step = 3;
        } else {
            if (data[i] != ')'.codePointAt(0)) {
                return null;
            }
            let ret = new GroupNode();
            ret.body = body;
            ret.capture = capture;
            ret.captureName = captureName;
            return {
                result: ret,
                index: i + 1,
            };
        }
    }
    return null;
}

function ParseCharacterClass(data: Uint32Array, index: number): { result: CharacterClassNode, index: number } | null {
    let i = index;
    let step = 0;
    let items = [];
    let withNot = false;
    while (i < data.length) {
        if (step == 0) {
            if (data[i] == '^'.codePointAt(0)) {
                withNot = true;
                i += 1;
            }
            step = 1;
        } else {
            if (data[i] == ']'.codePointAt(0)) {
                let ret = new CharacterClassNode();
                ret.without = withNot;
                ret.body = items;
                return {
                    result: ret,
                    index: i + 1,
                };
            } else {
                let rret = ParseRange(data, i);
                if (rret == null) {
                    return null;
                }
                items.push(rret.result);
                i = rret.index;
            }
        }
    }
    return null;
}

function ParseRange(data: Uint32Array, index: number): { result: ClassNode | CharNode | RangeNode, index: number } | null {
    let begin = ParseCommonChar(data, index);
    if (begin == null) {
        return null;
    }
    if (begin.result.type == 'class') {
        return begin;
    }
    if (begin.index >= data.length) {
        return null;
    }
    if (data[begin.index] != '-'.codePointAt(0)) {
        return begin;
    }
    let end = ParseCommonChar(data, begin.index + 1);
    if (end == null) {
        return null;
    }
    if (end.result.type == 'class') {
        return null;
    }
    let ret = new RangeNode();
    ret.begin = begin.result.char;
    ret.end = end.result.char;
    return {
        result: ret,
        index: end.index,
    };
}

const CommonCharEscapeMatcher = [ParseCharacterClassEscape, ParseBackspaceEscape, ParseCharacterEscape];
function ParseCommonChar(data: Uint32Array, index: number): { result: ClassNode | CharNode, index: number } | null {
    if (index >= data.length) {
        return null;
    }
    if (data[index] == ']'.codePointAt(0)) {
        return null;
    } else if (data[index] == '-'.codePointAt(0)) {
        return null;
    } else if (data[index] == '\\'.codePointAt(0)) {
        for (let matcher of CommonCharEscapeMatcher) {
            let ret = matcher(data, index + 1);
            if (ret != null) {
                return ret;
            }
        }
        return null;
    } else {
        let ret = new CharNode();
        ret.char = data[index];
        return {
            result: ret,
            index: index + 1,
        }
    }
}


function ParseBackspaceEscape(data: Uint32Array, index: number): { result: CharNode, index: number } | null {
    if (index >= data.length) {
        return null;
    }
    if (data[index] == 'b'.codePointAt(0)) {
        let ret = new CharNode();
        ret.char = '\b'.codePointAt(0)!;
        return {
            result: ret,
            index: index + 1,
        };
    }
    return null;
}
