module Main exposing (..)

import Array
import Browser exposing (..)
import Browser.Navigation exposing (..)
import Css
import Html.Styled exposing (..)
import Html.Styled.Attributes exposing (..)
import Html.Styled.Events exposing (..)
import Json.Decode as Decode exposing (Decoder, Value)
import MaterialColor
import Result
import Url exposing (Url)


type alias Flags =
    { initialValue : Maybe Value
    }


type Msg
    = DoNothing
    | ChangeSourceCode String
    | ChangeHatchState HatchState
    | SelectHatch Int


type alias Model =
    { mast : Maybe (Result String AST)
    , hatchState : HatchState
    }


type AST
    = Nodes (List AST)
    | Hatched Int AST
    | Raw String


main : Program Flags Model Msg
main =
    Browser.application
        { init = init
        , view = view
        , update = update
        , subscriptions = subscriptions
        , onUrlChange = always DoNothing
        , onUrlRequest = always DoNothing
        }


init : Flags -> Url -> Key -> ( Model, Cmd Msg )
init flags url _ =
    ( { mast =
            flags.initialValue
                |> Maybe.map
                    (\val ->
                        case Decode.decodeValue astDecoder val of
                            -- leftmap const
                            Ok decoded ->
                                Ok decoded

                            Err e ->
                                Err <| Decode.errorToString e
                    )
      , hatchState = None
      }
    , Cmd.none
    )


view : Model -> Document Msg
view model =
    { title = "BubblePop"
    , body =
        [ toUnstyled <|
            div
                [ css
                    [ Css.padding (Css.px 10)
                    , Css.margin (Css.px 0)
                    , Css.overflowX Css.hidden
                    , Css.overflowY Css.scroll
                    , Css.height (Css.vh 100)
                    , Css.width (Css.vw 100)
                    ]
                ]
                [ renderMAST model.hatchState model.mast
                , textarea
                    [ css
                        [ Css.resize Css.vertical
                        , Css.fontFamilies [ "monospace" ]
                        , Css.width (Css.pct 100)
                        , Css.minHeight (Css.em 20)
                        ]
                    , onInput ChangeSourceCode
                    ]
                    []
                ]
        ]
    }


renderMAST : HatchState -> Maybe (Result String AST) -> Html Msg
renderMAST hatchState mast =
    div
        [ css [ Css.fontFamilies [ "monospace" ], Css.fontWeight Css.bold, Css.fontSize (Css.em 2) ]
        , stopPropagationOn "mouseleave" <| Decode.succeed ( ChangeHatchState <| None, True )
        , stopPropagationOn "mouseup" <| Decode.succeed ( ChangeHatchState <| None, True )
        ]
        [ case mast of
            Nothing ->
                text "No source code has been specified!"

            Just (Err e) ->
                text <| "Err: " ++ e

            Just (Ok ast) ->
                renderAST hatchState ast
        ]


type HatchState
    = None
    | Active Int
    | Hover Int


renderAST : HatchState -> AST -> Html Msg
renderAST hatchState ast =
    case ast of
        Raw str ->
            text str

        Hatched hatch child ->
            span
                [ css <|
                    [ Css.backgroundColor <| hatchToColor hatch MaterialColor.S200
                    , Css.cursor Css.pointer
                    ]
                        ++ (case hatchState of
                                None ->
                                    []

                                Hover i ->
                                    if i == hatch then
                                        [ Css.backgroundColor <| hatchToColor hatch MaterialColor.S400 ]

                                    else
                                        []

                                Active i ->
                                    if i == hatch then
                                        [ Css.backgroundColor <| hatchToColor hatch MaterialColor.S800 ]

                                    else
                                        []
                           )
                , stopPropagationOn "click" <| Decode.succeed ( SelectHatch hatch, True )
                , stopPropagationOn "mouseover" <| Decode.succeed ( ChangeHatchState <| Hover hatch, True )
                , stopPropagationOn "mousedown" <| Decode.succeed ( ChangeHatchState <| Active hatch, True )
                , class (String.fromInt hatch)
                ]
                [ renderAST hatchState child ]

        Nodes children ->
            span [] <| List.map (renderAST hatchState) children


astDecoder : Decoder AST
astDecoder =
    Decode.oneOf
        [ Decode.map Nodes <| Decode.list <| Decode.lazy (\_ -> astDecoder)
        , Decode.map2 Hatched (Decode.field "hatch" Decode.int) (Decode.field "child" <| Decode.lazy (\_ -> astDecoder))
        , Decode.map Raw Decode.string
        ]


update : Msg -> Model -> ( Model, Cmd Msg )
update msg model =
    case msg of
        DoNothing ->
            ( model, Cmd.none )

        ChangeSourceCode str ->
            ( model, Cmd.none )

        -- TODO
        SelectHatch i ->
            let
                _ =
                    Debug.log "SelectHatch" i
            in
            ( model, Cmd.none )

        ChangeHatchState s ->
            ( { model | hatchState = s }, Cmd.none )


subscriptions : Model -> Sub msg
subscriptions model =
    Sub.none


hatchToColor : Int -> MaterialColor.Shade -> Css.Color
hatchToColor i shade =
    let
        arr =
            Array.fromList
                [ MaterialColor.Red shade
                , MaterialColor.Blue shade
                , MaterialColor.Purple shade
                , MaterialColor.Indigo shade
                , MaterialColor.Cyan shade
                , MaterialColor.Green shade
                , MaterialColor.Amber shade
                , MaterialColor.DeepOrange shade
                ]
    in
    MaterialColor.toCssColor <|
        Maybe.withDefault MaterialColor.White <|
            Array.get (modBy 8 i) arr
