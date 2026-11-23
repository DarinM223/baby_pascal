type
  TColor = record
    r: char;
    g: char;
    b: char;
    a: char;
  end;

  TTexture = record
    id: int32;
    width: int32;
    height: int32;
    format: int32;
  end;

var printChar : (char): void;
var printString : (^char): void;
var InitWindow : (int64, int64, ^char): void;
var CloseWindow : (): void;
var SetTargetFPS : (int64): void;
var WindowShouldClose : (): boolean;
var BeginDrawing : (): void;
var EndDrawing : (): void;
var ClearBackground : (TColor): void;
var DrawText : (^char, int64, int64, int64, TColor): void;

begin
  var RAYWHITE : TColor;
  var LIGHTGRAY : TColor;
  RAYWHITE.r := '\xF5';
  RAYWHITE.g := '\xF5';
  RAYWHITE.b := '\xF5';
  RAYWHITE.a := '\xFF';
  LIGHTGRAY.r := '\xC8';
  LIGHTGRAY.g := '\xC8';
  LIGHTGRAY.b := '\xC8';
  LIGHTGRAY.a := '\xFF';

  var width : int64 := 800;
  var height : int64 := 450;
  InitWindow(width, height, @"raylib window");
  SetTargetFPS(60);
  while not WindowShouldClose() do
  begin
    BeginDrawing();
      ClearBackground(RAYWHITE);
      DrawText(@"Congrats! You created your first window!", 190, 200, 20, LIGHTGRAY);
    EndDrawing();
  end;
  CloseWindow();
end