(* ::Package:: *)

(* ::Title:: *)
(*Make Rubi MX file*)


(* ::Subsubtitle:: *)
(*Run this package to generate a fast-loading Rubi.mx file that can be read using a Get ["Rubi.mx"] command.*)


(* ::Subsubtitle:: *)
(*To generate a ShowRubi.mx file that enables Rubi to display the steps required to integrate an expression, change the following assignment to True before running this package.*)


$LoadShowSteps = False;


Get[FileNameJoin[{DirectoryName[System`Private`$InputFileName],"Rubi.m"}]];


SetDirectory[DirectoryName[System`Private`$InputFileName]];
DumpSave[If[$LoadShowSteps===True, "StepRubi.mx", "Rubi.mx"], "Rubi`"];
ResetDirectory[];


(* ::Subsubtitle:: *)
(*Note that MX files cannot be exchanged between different operating systems or versions of Mathematica.*)
