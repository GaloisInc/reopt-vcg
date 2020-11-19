def pmovmskb : instruction :=
  definst "pmovmskb" $ do
    pattern fun (xmm_0 : reg (bv 128)) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 1)) <- eval (extract v_2 0 1);
      (v_4 : expression (bv 1)) <- eval (extract v_2 8 9);
      (v_5 : expression (bv 1)) <- eval (extract v_2 16 17);
      (v_6 : expression (bv 1)) <- eval (extract v_2 24 25);
      (v_7 : expression (bv 1)) <- eval (extract v_2 32 33);
      (v_8 : expression (bv 1)) <- eval (extract v_2 40 41);
      (v_9 : expression (bv 1)) <- eval (extract v_2 48 49);
      (v_10 : expression (bv 1)) <- eval (extract v_2 56 57);
      (v_11 : expression (bv 1)) <- eval (extract v_2 64 65);
      (v_12 : expression (bv 1)) <- eval (extract v_2 72 73);
      (v_13 : expression (bv 1)) <- eval (extract v_2 80 81);
      (v_14 : expression (bv 1)) <- eval (extract v_2 88 89);
      (v_15 : expression (bv 1)) <- eval (extract v_2 96 97);
      (v_16 : expression (bv 1)) <- eval (extract v_2 104 105);
      (v_17 : expression (bv 1)) <- eval (extract v_2 112 113);
      (v_18 : expression (bv 1)) <- eval (extract v_2 120 121);
      setRegister (lhs.of_reg r32_1) (concat (expression.bv_nat 16 0) (concat v_3 (concat v_4 (concat v_5 (concat v_6 (concat v_7 (concat v_8 (concat v_9 (concat v_10 (concat v_11 (concat v_12 (concat v_13 (concat v_14 (concat v_15 (concat v_16 (concat v_17 v_18))))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 1)) <- eval (extract v_2 0 1);
      (v_4 : expression (bv 1)) <- eval (extract v_2 8 9);
      (v_5 : expression (bv 1)) <- eval (extract v_2 16 17);
      (v_6 : expression (bv 1)) <- eval (extract v_2 24 25);
      (v_7 : expression (bv 1)) <- eval (extract v_2 32 33);
      (v_8 : expression (bv 1)) <- eval (extract v_2 40 41);
      (v_9 : expression (bv 1)) <- eval (extract v_2 48 49);
      (v_10 : expression (bv 1)) <- eval (extract v_2 56 57);
      (v_11 : expression (bv 1)) <- eval (extract v_2 64 65);
      (v_12 : expression (bv 1)) <- eval (extract v_2 72 73);
      (v_13 : expression (bv 1)) <- eval (extract v_2 80 81);
      (v_14 : expression (bv 1)) <- eval (extract v_2 88 89);
      (v_15 : expression (bv 1)) <- eval (extract v_2 96 97);
      (v_16 : expression (bv 1)) <- eval (extract v_2 104 105);
      (v_17 : expression (bv 1)) <- eval (extract v_2 112 113);
      (v_18 : expression (bv 1)) <- eval (extract v_2 120 121);
      setRegister (lhs.of_reg r64_1) (concat (expression.bv_nat 48 0) (concat v_3 (concat v_4 (concat v_5 (concat v_6 (concat v_7 (concat v_8 (concat v_9 (concat v_10 (concat v_11 (concat v_12 (concat v_13 (concat v_14 (concat v_15 (concat v_16 (concat v_17 v_18))))))))))))))));
      pure ()
    pat_end
