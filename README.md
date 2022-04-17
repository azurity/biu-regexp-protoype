# prototype of RegExp of mobius in typesciprt language

typescript写的mobius要用的RegExp的原型，用于修正算法

> `unicode.ts`是对mobius的unicode模块的模拟

## 语法

- 基于ECMAscript RegExp 语法
- 没有捕获组的引用`\`_`n`_, `\k<`_`name`_`>`之类的
- 只有ignoreCase, 和multiline两个模式位，强制unicode模式
- 额外增加了`\e`来转义`\x1B`
