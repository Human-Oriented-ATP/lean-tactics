window;import{jsxs as t,jsx as e}from"react/jsx-runtime";import*as n from"react";const o=n.createContext(0);function r(){let e=n.useContext(o);return t("p",{children:["Component A with context value ",e,"."]})}function i(){let e=n.useContext(o);return t("p",{children:["Component B with context value ",e,"."]})}function c(){t(o.Provider,{value:5,children:[e(r,{}),e(i,{})]})}export{c as CombinedComponentTest,r as ComponentA,i as ComponentB,o as CustomContext};