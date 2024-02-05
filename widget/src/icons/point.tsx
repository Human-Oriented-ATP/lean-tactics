import * as React from "react";
const SvgPoint = (props:any) => (
  <svg xmlns="http://www.w3.org/2000/svg" width={32} height={32} {...props}>
    <circle
      cx={16}
      cy={16}
      r={3.506}
      style={{
        fill: "#b3e741",
        fillOpacity: 1,
        stroke: "#000",
        strokeWidth: 1.028,
        strokeLinecap: "butt",
        strokeLinejoin: "miter",
        strokeMiterlimit: 4,
        strokeDasharray: "none",
        strokeDashoffset: 4.5232001,
        strokeOpacity: 1,
      }}
    />
  </svg>
);
export default SvgPoint;

