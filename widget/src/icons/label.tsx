import * as React from "react";
const SvgLabel = (props:any) => (
  <svg
    xmlns="http://www.w3.org/2000/svg"
    xmlnsXlink="http://www.w3.org/1999/xlink"
    width={32}
    height={32}
    viewBox="0 0 24 24"
    {...props}
  >
    <defs>
      <symbol
        id="label_svg__a"
        overflow="visible"
        style={{
          overflow: "visible",
        }}
      >
        <path
          d="M2.063-.469 1.984 0H-.875l.078-.422.875-.219L5.406-11h1.5L8.86-.64l.97.218L9.75 0H6.031l.094-.469 1.11-.234-.5-3.438H2.608L1.016-.703zm3.593-9.781L2.97-4.86h3.64zm0 0"
          style={{
            stroke: "none",
          }}
        />
      </symbol>
    </defs>
    <use
      xlinkHref="#label_svg__a"
      width="100%"
      height="100%"
      x={261.207}
      y={221.523}
      style={{
        fill: "#000",
        fillOpacity: 1,
        strokeWidth: 0.806464,
      }}
      transform="translate(-318 -256.128)scale(1.23998)"
    />
  </svg>
);
export default SvgLabel;

