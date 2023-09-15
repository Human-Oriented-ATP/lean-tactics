import * as React from 'react'
import { EditorContext, PanelWidgetProps } from '@leanprover/infoview'
import { Position, TextDocumentEdit } from 'vscode-languageserver-protocol'
import { Button, Grid, Typography, ButtonPropsVariantOverrides, ButtonPropsColorOverrides, ButtonPropsSizeOverrides, GridDirection, GridSpacing } from '@mui/material'
import { OverridableStringUnion } from '@mui/types'
import { ResponsiveStyleValue } from '@mui/system'

/-- Structure for rendering Grids with Buttons -/
interface GridProps 
{
  direction : ResponsiveStyleValue<GridDirection>
  spacing : ResponsiveStyleValue<GridSpacing>
}

/-- Structure for rendering Typography objects with Buttons -/
interface TypographyProps {
    variant : String
    display : String
    mt :  Number
}

/-- Structure for rendering the display Button objects with Buttons -/
interface DisplayButtonProps
{
  variant : OverridableStringUnion<'text' | 'outlined' | 'contained', ButtonPropsVariantOverrides>
  color : OverridableStringUnion<'inherit' | 'primary' | 'secondary' | 'success' | 'error' | 'info' | 'warning', ButtonPropsColorOverrides >
  size : OverridableStringUnion<'small' | 'medium' | 'large', ButtonPropsSizeOverrides>
  container : boolean
  item : boolean
}

interface ButtonPropsBundle 
{
  gridProps : GridProps
  typoProps : TypographyProps
  displayButtonProps : DisplayButtonProps
}

interface MakeEditButtonLinkProps {
  edit : TextDocumentEdit
  newCursorPos? : Position
  title? : string
  buttonProps : ButtonPropsBundle
}

interface MakeEditButtonsLinkProps extends PanelWidgetProps {
  buttonProps : MakeEditButtonLinkProps[]
}

/** A Button UI component that calls the `insertText` function when clicked. */
function InsertionButton(props:MakeEditButtonLinkProps): JSX.Element {
    const buttonProps = props.buttonProps.displayButtonProps
    const ec = React.useContext(EditorContext)
    return (<Button
      variant= {buttonProps.variant}
      color= {buttonProps.color}
      size= {buttonProps.size}
      style={{ textTransform: 'none' }}
      title = {props.title ?? ''}
      onClick={async () => {
        await ec.api.applyEdit({ documentChanges: [props.edit] })
        // TODO: https://github.com/leanprover/vscode-lean4/issues/225
        if (props.newCursorPos)
          await ec.revealPosition({ ...props.newCursorPos, uri: props.edit.textDocument.uri })
      }}>
        {props.title}
        </Button>);
  }


export default function(props: MakeEditButtonsLinkProps) {
  let buttonProps = props.buttonProps
  return (
  <details open={true}>
    <summary> Motivated proof interface </summary>
    <Typography variant="button" display="block" mt={2} gutterBottom>
      Proof-generating moves
    </Typography>
    <Grid container = {buttonProps[0].buttonProps.displayButtonProps.container} direction = {buttonProps[0].buttonProps.gridProps.direction} spacing={buttonProps[0].buttonProps.gridProps.spacing}>
    { buttonProps.map ((prop) => {
            if (props.selectedLocations.length == 1)
            return (
              <Grid item = {prop.buttonProps.displayButtonProps.item} >
              <InsertionButton edit = {prop.edit} newCursorPos = {prop.newCursorPos} title = {prop.title} buttonProps = {prop.buttonProps} />
              </Grid>);
        }) }
    </Grid>
    </details>);
}