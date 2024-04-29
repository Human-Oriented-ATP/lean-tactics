window;import{jsxs as e,jsx as n,Fragment as t}from"react/jsx-runtime";import*as r from"react";import{RpcContext as i,useAsyncPersistent as o,mapRpcError as u,importWidgetModule as c,EditorContext as s}from"@leanprover/infoview";var a=function(){return a=Object.assign||function(e){for(var n,t=1,r=arguments.length;t<r;t++)for(var i in n=arguments[t])Object.prototype.hasOwnProperty.call(n,i)&&(e[i]=n[i]);return e},a.apply(this,arguments)};function l(e,n,t,r){return new(t||(t=Promise))((function(i,o){function u(e){try{s(r.next(e))}catch(e){o(e)}}function c(e){try{s(r.throw(e))}catch(e){o(e)}}function s(e){var n;e.done?i(e.value):(n=e.value,n instanceof t?n:new t((function(e){e(n)}))).then(u,c)}s((r=r.apply(e,n||[])).next())}))}function f(e,n){var t,r,i,o,u={label:0,sent:function(){if(1&i[0])throw i[1];return i[1]},trys:[],ops:[]};return o={next:c(0),throw:c(1),return:c(2)},"function"==typeof Symbol&&(o[Symbol.iterator]=function(){return this}),o;function c(c){return function(s){return function(c){if(t)throw new TypeError("Generator is already executing.");for(;o&&(o=0,c[0]&&(u=0)),u;)try{if(t=1,r&&(i=2&c[0]?r.return:c[0]?r.throw||((i=r.return)&&i.call(r),0):r.next)&&!(i=i.call(r,c[1])).done)return i;switch(r=0,i&&(c=[2&c[0],i.value]),c[0]){case 0:case 1:i=c;break;case 4:return u.label++,{value:c[1],done:!1};case 5:u.label++,r=c[1],c=[0];continue;case 7:c=u.ops.pop(),u.trys.pop();continue;default:if(!(i=u.trys,(i=i.length>0&&i[i.length-1])||6!==c[0]&&2!==c[0])){u=0;continue}if(3===c[0]&&(!i||c[1]>i[0]&&c[1]<i[3])){u.label=c[1];break}if(6===c[0]&&u.label<i[1]){u.label=i[1],i=c;break}if(i&&u.label<i[2]){u.label=i[2],u.ops.push(c);break}i[2]&&u.ops.pop(),u.trys.pop();continue}c=n.call(e,u)}catch(e){c=[6,e],r=0}finally{t=i=0}if(5&c[0])throw c[1];return{value:c[0]?c[1]:void 0,done:!0}}([c,s])}}}function d(i,o,u){return l(this,void 0,void 0,(function(){var s,p,h,v,m,w,g,b,y,x,E,C,P,k,S,j,U,L=this;return f(this,(function(N){switch(N.label){case 0:return"text"in u?[2,n(t,{children:u.text})]:[3,1];case 1:if(!("element"in u))return[3,3];for(s=u.element,p=s[0],h=s[1],k=s[2],v={},m=0,w=h;m<w.length;m++)g=w[m],b=g[0],y=g[1],v[b]=y;return[4,Promise.all(k.map((function(e){return l(L,void 0,void 0,(function(){return f(this,(function(n){switch(n.label){case 0:return[4,d(i,o,e)];case 1:return[2,n.sent()]}}))}))})))];case 2:return S=N.sent(),"hr"===p?[2,n("hr",{})]:0===S.length?[2,r.createElement(p,v)]:[2,r.createElement(p,v,S)];case 3:return"component"in u?(x=u.component,E=x[0],C=x[1],P=x[2],k=x[3],[4,Promise.all(k.map((function(e){return l(L,void 0,void 0,(function(){return f(this,(function(n){switch(n.label){case 0:return[4,d(i,o,e)];case 1:return[2,n.sent()]}}))}))})))]):[3,6];case 4:return S=N.sent(),j=a(a({},P),{pos:o}),[4,c(i,o,E)];case 5:if(U=N.sent(),!(C in U))throw new Error("Module '".concat(E,"' does not export '").concat(C,"'"));return 0===S.length?[2,r.createElement(U[C],j)]:[2,r.createElement(U[C],j,S)];case 6:return[2,e("span",a({className:"red"},{children:["Unknown HTML variant: ",JSON.stringify(u)]}))];case 7:return[2]}}))}))}function p(c){var s=c.pos,l=c.html,f=r.useContext(i),p=o((function(){return d(f,s,l)}),[f,s,l]);return"resolved"===p.state?p.value:"rejected"===p.state?e("span",a({className:"red"},{children:["Error rendering HTML: ",u(p.error).message]})):n(t,{})}"function"==typeof SuppressedError&&SuppressedError;var h=r.createContext({answer:function(e){console.warn("Uncaptured answer: ".concat(e))},pos:{uri:"dummy",line:0,character:0}});function v(e){return n("div",{children:n("p",{children:"No questions..."})})}function m(e){var t=r.useContext(h);var i=r.useRef(null);return r.useEffect((function(){null!==i.current&&i.current.reset()}),[e.elems]),n("form",a({onSubmit:function(e){e.preventDefault();var n=new FormData(e.currentTarget);t.answer(Object.fromEntries(n))},ref:i},{children:e.elems.map((function(e){return n(p,{pos:t.pos,html:e})}))}))}function w(e,n){if(!("element"in e))return e;var t=e.element,r=t[0],i=t[1],o=t[2];if("button"==r||"a"==r){var u=i.slice();return"a"==r&&u.push(["className","pointer dim"]),u.push(["onClick",n]),{element:[r,u,o]}}return{element:[r,i,o.map((function(e){return w(e,n)}))]}}function g(e){return n(p,{html:w(e.html,e.onClick),pos:e.pos})}function b(t){var i=r.useRef(null),o=r.useContext(h);return e("div",{children:[n(p,{pos:o.pos,html:t.question}),n("div",a({ref:i},{children:t.options.map((function(e,t){return n(g,{html:e,pos:o.pos,onClick:function(){return o.answer(t)}})}))}))]})}var y={level:0,editPos:{line:0,character:0},widget:n("p",{children:"Initializing..."})};function x(t){var o=r.useState(y),u=o[0],c=o[1],d=r.useContext(i),v=r.useContext(s),m=r.useRef({line:0,character:0}),w=r.useRef(null);function g(e,n){if(null!==w.current){if(e!==m.current||0!=n.length){var t={start:e,end:m.current},r=n.map((function(e){return e+"\n"})).join("");0==n.length?m.current=e:m.current={line:e.line+n.length,character:0},0!=e.character&&(r="\n"+r,m.current={line:m.current.line+1,character:0}),function(e,n){l(this,void 0,void 0,(function(){return f(this,(function(t){switch(t.label){case 0:return[4,v.api.applyEdit({documentChanges:[e]})];case 1:return t.sent(),[4,v.revealPosition(n)];case 2:return t.sent(),[2]}}))}))}({textDocument:w.current.ident,edits:[{range:t,newText:r}]},a(a({},m.current),{uri:w.current.ident.uri}))}}else n.length>0&&(console.warn("Document editing not initialized, cannot insert:"),console.warn(n))}function b(e,r,i,o){var u=m.current;for(var s=n(h.Provider,a({value:{answer:function(e){return l(this,void 0,void 0,(function(){var n,t,r,i;return f(this,(function(s){switch(s.label){case 0:console.log("Answer:"),console.log(e),n=o,t=[],s.label=1;case 1:return[4,d.call("processUserAnswer",[e,n])];case 2:if(r=s.sent(),i=r[0],n=r[1],e=null,"insertLine"in i)t.push(i.insertLine.line);else{if(!("initEdit"in i))return g(u,t),c(b(w,i.widget.level,i.widget.w,n)),[3,3];console.warn("initEdit is only available suring initialization")}return[3,1];case 3:return[2]}}))}))},pos:t.pos}},{children:n(p,{html:i,pos:t.pos})})),v=e;void 0!==v&&v.level>=r;)v=v.parent;var w={level:r,widget:s,editPos:u,parent:v,previous:e};return w}function x(){return l(this,void 0,void 0,(function(){var e,n,r,i;return f(this,(function(o){switch(o.label){case 0:return[4,d.call("initializeInteraction",t.code)];case 1:e=o.sent(),n=e[0],r=e[1],w.current=null,o.label=2;case 2:if("insertLine"in n)console.warn("Edits disabled before user action");else{if(!("initEdit"in n))return w.current&&(m.current=w.current.startPos),c(b(void 0,n.widget.level,n.widget.w,r)),[3,4];w.current=n.initEdit}return[4,d.call("processUserAnswer",[null,r])];case 3:return i=o.sent(),n=i[0],r=i[1],[3,2];case 4:return[2]}}))}))}r.useEffect((function(){x()}),[t.pos.line]);for(var E=[],C=u;void 0!==C;)E.push(C.widget),C=C.parent;return E.reverse(),e("div",{children:[n("button",a({onClick:function(){console.log("Undo"),console.log(u),void 0!==u.previous&&(g(u.previous.editPos,[]),c(u.previous))}},{children:"Undo"})),n("hr",{}),E]})}export{v as EmptyWidget,m as FormWidget,b as SelectWidget,x as default};