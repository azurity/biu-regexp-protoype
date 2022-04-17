const iconv = require('iconv-lite');
import { MatchResult, RegAST, ParsePattern, MatchResultSet } from "./ast";
export { FlagDefault, FlagIgnoreICase, FlagMultiline } from "./ast";


function _prepareStr(s: string) {
    return new Uint32Array(iconv.encode(s, 'UTF-32', { addBOM: false }).buffer);
}

export class BiuRegExp {
    ast: RegAST;
    flag: number;
    constructor(re: string, flags: number) {
        let ret = ParsePattern(_prepareStr(re));
        if (ret == null) {
            throw "error";
        }
        this.ast = ret;
        this.ast.allocCapture(1);
        this.flag = flags;
    }
    exec(data: string | Uint32Array): MatchResultSet | null {
        if (data === null) {
            throw "";
        }
        if (typeof data == 'string') {
            data = _prepareStr(data as string);
        }
        for (let i = 0; i < data.length; i++) {
            let ret = this.ast.match(data as Uint32Array, i, { value: null }, { direct: 1, flag: this.flag });
            if (ret != null) {
                ret.result.set(0, {
                    result: iconv.decode(Buffer.from(data.slice(i, ret.index).buffer), 'UTF-32'),
                    position: i,
                });
                return ret.result;
            }
        }
        return null;
    }
    test(data: string) {
        return this.exec(data) !== null;
    }
}

export function match(s: string, matcher: BiuRegExp): string | null {
    let ret = matcher.exec(s);
    if (ret === null) {
        return null;
    }
    else {
        return ret.get(0)!.result;
    }
}

export function matchAll(s: string, matcher: BiuRegExp): string[] {
    let ret = [];
    let prepared = _prepareStr(s);
    let index = 0;
    while (true) {
        // need slice!!!
        let result = matcher.exec(prepared.slice(index));
        if (result === null) {
            break;
        }
        ret.push(result.get(0)!.result);
        index += Math.max(_prepareStr(result.get(0)!.result).length, 1);
    }
    return ret;
}

export function search(s: string, matcher: BiuRegExp): number {
    let ret = matcher.exec(s);
    if (ret === null) {
        return -1;
    }
    else {
        return ret.get(0)!.position;
    }
}
