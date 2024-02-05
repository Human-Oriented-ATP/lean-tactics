import * as React from "react";
const SvgCircle = (props:any) => (
  <svg xmlns="http://www.w3.org/2000/svg" width={32} height={32} {...props}>
    <circle
      cx={16}
      cy={16}
      r={12}
      style={{
        fill: "none",
        fillOpacity: 1,
        stroke: "#000",
        strokeWidth: 3.56799946,
        strokeLinecap: "butt",
        strokeLinejoin: "miter",
        strokeMiterlimit: 4,
        strokeDasharray: "none",
        strokeDashoffset: 6.65196865,
        strokeOpacity: 1,
      }}
    />
    <circle
      cx={16}
      cy={16}
      r={2.063}
      style={{
        fill: "#000",
        fillOpacity: 1,
        stroke: "none",
        strokeWidth: 1.51181102,
        strokeLinecap: "butt",
        strokeLinejoin: "miter",
        strokeMiterlimit: 4,
        strokeDasharray: "4.53543305,4.53543305",
        strokeDashoffset: 6.65196848,
        strokeOpacity: 0.97533629,
      }}
    />
    <circle
      cx={16}
      cy={16}
      r={12}
      style={{
        fill: "none",
        fillOpacity: 1,
        stroke: "#b3e741",
        strokeWidth: 1.51181102,
        strokeLinecap: "butt",
        strokeLinejoin: "miter",
        strokeMiterlimit: 4,
        strokeDasharray: "none",
        strokeDashoffset: 6.65196865,
        strokeOpacity: 1,
      }}
    />
  </svg>
);
export default SvgCircle;

