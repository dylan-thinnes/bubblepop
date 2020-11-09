port module Main exposing (..)

import Array
import Browser exposing (..)
import Browser.Navigation exposing (..)
import Css
import Html.Styled exposing (..)
import Html.Styled.Attributes exposing (..)
import Html.Styled.Events exposing (..)
import Http
import Json.Decode as Decode exposing (Decoder, Value)
import Json.Encode as Encode
import MaterialColor
import Murmur3
import Result
import Url exposing (Url)


type alias Flags =
    { initialValue : Maybe Value
    }


type Msg
    = DoNothing
    | ChangeSourceCode String
    | ChangeCrumbState CrumbState
    | SelectCrumb Crumbtrail
    | GotHTTPAST (Result.Result Http.Error AST)
    | ResetExpr


type alias Model =
    { mast : Maybe (Result String AST)
    , liveCrumb : CrumbState
    , originalUrl : Url
    }


type AST
    = Nodes (List AST)
    | Crumbed Crumbtrail AST
    | Raw String


type Crumb
    = AppFunc
    | AppArg Int
    | AbsBody
    | IfCond
    | IfTrue
    | IfFalse
    | LetBound
    | LetBody
    | EConsArg Int
    | CaseBody
    | CaseBranch Int
    | AnnCont


type alias Crumbtrail =
    List Crumb


type CrumbState
    = None
    | Active Crumbtrail
    | Hover Crumbtrail


encodeCrumbtrail : Crumbtrail -> Value
encodeCrumbtrail =
    Encode.list Encode.string << List.map crumbToString


crumbtrailToString : Crumbtrail -> String
crumbtrailToString crumbtrail =
    "crumbtrail_" ++ String.join "_" (List.map crumbToString crumbtrail)


crumbToTagString : Crumb -> String
crumbToTagString c =
    case c of
        AppFunc ->
            "AppFunc"

        AppArg i ->
            "AppArg"

        AbsBody ->
            "AbsBody"

        IfCond ->
            "IfCond"

        IfTrue ->
            "IfTrue"

        IfFalse ->
            "IfFalse"

        LetBound ->
            "LetBound"

        LetBody ->
            "LetBody"

        EConsArg i ->
            "EConsArg"

        CaseBody ->
            "CaseBody"

        AnnCont ->
            "AnnCont"

        CaseBranch i ->
            "CaseBranch"


crumbToString : Crumb -> String
crumbToString c =
    case c of
        AppArg i ->
            crumbToTagString c ++ " " ++ String.fromInt i

        EConsArg i ->
            crumbToTagString c ++ " " ++ String.fromInt i

        CaseBranch i ->
            crumbToTagString c ++ " " ++ String.fromInt i

        _ ->
            crumbToTagString c


crumbtrailDecoder : Decoder Crumbtrail
crumbtrailDecoder =
    Decode.list crumbDecoder


crumbDecoder : Decoder Crumb
crumbDecoder =
    let
        stringThenRest head handler =
            Decode.string
                |> Decode.andThen
                    (\s ->
                        if String.startsWith head s then
                            handler (String.dropLeft (String.length head) s)

                        else
                            Decode.fail ("Could not parse string starting with '" ++ head ++ "'.")
                    )

        autoString head value =
            stringThenRest head
                (\rest ->
                    if String.length rest == 0 then
                        Decode.succeed value

                    else
                        Decode.fail ("Unexpected trailing '" ++ rest ++ "' on '" ++ head ++ "'.")
                )

        autoStringAndInt head handler =
            stringThenRest head
                (\rest ->
                    case String.toInt (String.dropLeft 1 rest) of
                        Just i ->
                            Decode.succeed <| handler i

                        Nothing ->
                            Decode.fail <| "Could not read a following int for '" ++ head ++ "' in '" ++ rest ++ "'"
                )
    in
    Decode.oneOf
        [ autoString (crumbToTagString AppFunc) AppFunc
        , autoStringAndInt (crumbToTagString (AppArg 0)) AppArg
        , autoString (crumbToTagString AbsBody) AbsBody
        , autoString (crumbToTagString IfCond) IfCond
        , autoString (crumbToTagString IfTrue) IfTrue
        , autoString (crumbToTagString IfFalse) IfFalse
        , autoString (crumbToTagString LetBound) LetBound
        , autoString (crumbToTagString LetBody) LetBody
        , autoStringAndInt (crumbToTagString (EConsArg 0)) EConsArg
        , autoString (crumbToTagString CaseBody) CaseBody
        , autoStringAndInt (crumbToTagString (CaseBranch 0)) CaseBranch
        , autoString (crumbToTagString AnnCont) AnnCont
        ]


crumbtrailToHash : Crumbtrail -> Int
crumbtrailToHash =
    Murmur3.hashString 0 << crumbtrailToString


crumbtrailToColor : Crumbtrail -> MaterialColor.Shade -> Css.Color
crumbtrailToColor trail shade =
    let
        hash =
            crumbtrailToHash trail

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
            Array.get (modBy 8 hash) arr



--stringToCrumb :: String -> Maybe Crumb


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
      , liveCrumb = None
      , originalUrl = url
      }
    , getNext { url | path = "/get" } Nothing
    )


getNext : Url -> Maybe Crumbtrail -> Cmd Msg
getNext url mtrail =
    case mtrail of
        Just trail ->
            Http.post
                { url = Url.toString url
                , expect = Http.expectJson GotHTTPAST astDecoder
                , body = Http.jsonBody <| encodeCrumbtrail trail
                }

        Nothing ->
            Http.get
                { url = Url.toString url
                , expect = Http.expectJson GotHTTPAST astDecoder
                }


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
                [ renderMAST model.liveCrumb model.mast
                , button [ onClick ResetExpr ] [ text "Reset expression" ]
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


renderMAST : CrumbState -> Maybe (Result String AST) -> Html Msg
renderMAST liveCrumb mast =
    div
        [ css [ Css.fontFamilies [ "monospace" ], Css.fontWeight Css.bold, Css.fontSize (Css.em 2) ]
        , stopPropagationOn "mouseleave" <| Decode.succeed ( ChangeCrumbState <| None, True )
        , stopPropagationOn "mouseup" <| Decode.succeed ( ChangeCrumbState <| None, True )
        ]
        [ pre []
            [ case mast of
                Nothing ->
                    text "No source code has been specified!"

                Just (Err e) ->
                    text <| "Err: " ++ e

                Just (Ok ast) ->
                    renderAST liveCrumb ast
            ]
        ]


renderAST : CrumbState -> AST -> Html Msg
renderAST liveCrumb ast =
    case ast of
        Raw str ->
            text str

        Crumbed crumbtrail child ->
            span
                [ css <|
                    [ Css.backgroundColor <| crumbtrailToColor crumbtrail MaterialColor.S200
                    , Css.cursor Css.pointer
                    ]
                        ++ (case liveCrumb of
                                None ->
                                    []

                                Hover i ->
                                    if i == crumbtrail then
                                        [ Css.backgroundColor <| crumbtrailToColor crumbtrail MaterialColor.S400 ]

                                    else
                                        []

                                Active i ->
                                    if i == crumbtrail then
                                        [ Css.backgroundColor <| crumbtrailToColor crumbtrail MaterialColor.S800 ]

                                    else
                                        []
                           )
                , stopPropagationOn "click" <| Decode.succeed ( SelectCrumb crumbtrail, True )
                , stopPropagationOn "mouseover" <| Decode.succeed ( ChangeCrumbState <| Hover crumbtrail, True )
                , stopPropagationOn "mousedown" <| Decode.succeed ( ChangeCrumbState <| Active crumbtrail, True )

                -- , class crumbtrail
                ]
                [ renderAST liveCrumb child ]

        Nodes children ->
            span [] <| List.map (renderAST liveCrumb) children


astDecoder : Decoder AST
astDecoder =
    Decode.oneOf
        [ Decode.map Nodes <| Decode.list <| Decode.lazy (\_ -> astDecoder)
        , Decode.map2 Crumbed (Decode.field "crumbtrail" crumbtrailDecoder) (Decode.field "child" <| Decode.lazy (\_ -> astDecoder))
        , Decode.map Raw Decode.string
        ]


update : Msg -> Model -> ( Model, Cmd Msg )
update msg model =
    case msg of
        DoNothing ->
            ( model, Cmd.none )

        ChangeSourceCode str ->
            ( model, Cmd.none )

        SelectCrumb trail ->
            let
                { originalUrl } =
                    model
            in
            ( model, getNext { originalUrl | path = "/trail" } (Just trail) )

        ResetExpr ->
            let
                { originalUrl } =
                    model
            in
            ( model, getNext { originalUrl | path = "/reset" } Nothing )

        ChangeCrumbState c ->
            ( { model | liveCrumb = c }, Cmd.none )

        GotHTTPAST ast ->
            ( { model | mast = Just <| Result.mapError Debug.toString ast }, Cmd.none )


subscriptions : Model -> Sub msg
subscriptions model =
    Sub.none


port send : Value -> Cmd msg
