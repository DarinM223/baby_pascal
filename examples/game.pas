var printChar : (char): void;
var printString : (*char): void;
var InitWindow : (integer, integer, *char): void;
var CloseWindow : (): void;
var SetTargetFPS : (integer): void;
var WindowShouldClose : (): boolean;
var BeginDrawing : (): void;
var EndDrawing : (): void;
var ClearBackground : ({r: char, g: char, b: char, a: char}): void;
var DrawText : ( *char, integer, integer, integer, { r: char, g: char, b: char, a: char }): void;

begin
  var RAYWHITE : { r: char, g: char, b: char, a: char };
  RAYWHITE.r := '\xF5';
  RAYWHITE.g := '\xF5';
  RAYWHITE.b := '\xF5';
  RAYWHITE.a := '\xFF';
  var LIGHTGRAY : { r: char, g: char, b: char, a: char };
  LIGHTGRAY.r := '\xC8';
  LIGHTGRAY.g := '\xC8';
  LIGHTGRAY.b := '\xC8';
  LIGHTGRAY.a := '\xFF';

  width := 800;
  height := 450;
  InitWindow(width, height, &"raylib window");
  SetTargetFPS(60);
  while not WindowShouldClose() do
  begin
    BeginDrawing();
      ClearBackground(RAYWHITE);
      DrawText(&"Congrats! You created your first window!", 190, 200, 20, LIGHTGRAY);
    EndDrawing();
  end;
  CloseWindow();
end