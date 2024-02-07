import * as React from 'react';

export const CustomContext = React.createContext(0)

export function ComponentA() {
    let ctx = React.useContext(CustomContext);
    return <p>Component A with context value {ctx}.</p>
}

export function ComponentB() {
    let ctx = React.useContext(CustomContext);
    return <p>Component B with context value {ctx}.</p>
}

export function CombinedComponentTest() {
    return <CustomContext.Provider value={5}>
        <ComponentA />
        <ComponentB />
    </CustomContext.Provider>
}
export default CombinedComponentTest
