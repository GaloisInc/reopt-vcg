def pminsd1 : instruction :=
  definst "pminsd" $ do
    pattern fun (v_2611 : reg (bv 128)) (v_2612 : reg (bv 128)) => do
      v_5170 <- getRegister v_2612;
      v_5171 <- eval (extract v_5170 0 32);
      v_5172 <- getRegister v_2611;
      v_5173 <- eval (extract v_5172 0 32);
      v_5176 <- eval (extract v_5170 32 64);
      v_5177 <- eval (extract v_5172 32 64);
      v_5180 <- eval (extract v_5170 64 96);
      v_5181 <- eval (extract v_5172 64 96);
      v_5184 <- eval (extract v_5170 96 128);
      v_5185 <- eval (extract v_5172 96 128);
      setRegister (lhs.of_reg v_2612) (concat (mux (slt v_5171 v_5173) v_5171 v_5173) (concat (mux (slt v_5176 v_5177) v_5176 v_5177) (concat (mux (slt v_5180 v_5181) v_5180 v_5181) (mux (slt v_5184 v_5185) v_5184 v_5185))));
      pure ()
    pat_end;
    pattern fun (v_2606 : Mem) (v_2607 : reg (bv 128)) => do
      v_12552 <- getRegister v_2607;
      v_12553 <- eval (extract v_12552 0 32);
      v_12554 <- evaluateAddress v_2606;
      v_12555 <- load v_12554 16;
      v_12556 <- eval (extract v_12555 0 32);
      v_12559 <- eval (extract v_12552 32 64);
      v_12560 <- eval (extract v_12555 32 64);
      v_12563 <- eval (extract v_12552 64 96);
      v_12564 <- eval (extract v_12555 64 96);
      v_12567 <- eval (extract v_12552 96 128);
      v_12568 <- eval (extract v_12555 96 128);
      setRegister (lhs.of_reg v_2607) (concat (mux (slt v_12553 v_12556) v_12553 v_12556) (concat (mux (slt v_12559 v_12560) v_12559 v_12560) (concat (mux (slt v_12563 v_12564) v_12563 v_12564) (mux (slt v_12567 v_12568) v_12567 v_12568))));
      pure ()
    pat_end
