var printChar : (char): void;
var printString : (*char): void;
var InitWindow : (integer, integer, *char): void;
var CloseWindow : (): void;
var SetTargetFPS : (integer): void;
var WindowShouldClose : (): boolean;
var BeginDrawing : (): void;
var EndDrawing : (): void;
var ClearBackground : (integer): void;
var DrawText : (*char, integer, integer, integer, integer): void;

begin
  width := 800;
  height := 450;
  InitWindow(width, height, &"raylib window");
  SetTargetFPS(60);
  while not WindowShouldClose() do
  begin
    BeginDrawing();
      ClearBackground(0xF5F5F5FF);
      DrawText(&"Congrats! You created your first window!", 190, 200, 20, 0xC8C8C8FF);
    EndDrawing();
  end;
  CloseWindow();
end