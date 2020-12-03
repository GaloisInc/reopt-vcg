def pmaddwd : instruction :=
  definst "pmaddwd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let (v_4 : expression (bv 16)) <- eval (extract v_3 16 32);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 16)) <- eval (extract v_5 16 32);
      let (v_7 : expression (bv 16)) <- eval (extract v_3 0 16);
      let (v_8 : expression (bv 16)) <- eval (extract v_5 0 16);
      let (v_9 : expression (bv 16)) <- eval (extract v_3 48 64);
      let (v_10 : expression (bv 16)) <- eval (extract v_5 48 64);
      let (v_11 : expression (bv 16)) <- eval (extract v_3 32 48);
      let (v_12 : expression (bv 16)) <- eval (extract v_5 32 48);
      let (v_13 : expression (bv 16)) <- eval (extract v_3 80 96);
      let (v_14 : expression (bv 16)) <- eval (extract v_5 80 96);
      let (v_15 : expression (bv 16)) <- eval (extract v_3 64 80);
      let (v_16 : expression (bv 16)) <- eval (extract v_5 64 80);
      let (v_17 : expression (bv 16)) <- eval (extract v_3 112 128);
      let (v_18 : expression (bv 16)) <- eval (extract v_5 112 128);
      let (v_19 : expression (bv 16)) <- eval (extract v_3 96 112);
      let (v_20 : expression (bv 16)) <- eval (extract v_5 96 112);
      let v_21 <- eval (concat (add (mul (sext v_13 32) (sext v_14 32)) (mul (sext v_15 32) (sext v_16 32))) (add (mul (sext v_17 32) (sext v_18 32)) (mul (sext v_19 32) (sext v_20 32))));
      let v_22 <- eval (concat (add (mul (sext v_9 32) (sext v_10 32)) (mul (sext v_11 32) (sext v_12 32))) v_21);
      let v_23 <- eval (concat (add (mul (sext v_4 32) (sext v_6 32)) (mul (sext v_7 32) (sext v_8 32))) v_22);
      setRegister (lhs.of_reg xmm_1) v_23;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 16)) <- eval (extract v_2 16 32);
      let v_4 <- getRegister (lhs.of_reg xmm_1);
      let (v_5 : expression (bv 16)) <- eval (extract v_4 16 32);
      let (v_6 : expression (bv 16)) <- eval (extract v_2 0 16);
      let (v_7 : expression (bv 16)) <- eval (extract v_4 0 16);
      let (v_8 : expression (bv 16)) <- eval (extract v_2 48 64);
      let (v_9 : expression (bv 16)) <- eval (extract v_4 48 64);
      let (v_10 : expression (bv 16)) <- eval (extract v_2 32 48);
      let (v_11 : expression (bv 16)) <- eval (extract v_4 32 48);
      let (v_12 : expression (bv 16)) <- eval (extract v_2 80 96);
      let (v_13 : expression (bv 16)) <- eval (extract v_4 80 96);
      let (v_14 : expression (bv 16)) <- eval (extract v_2 64 80);
      let (v_15 : expression (bv 16)) <- eval (extract v_4 64 80);
      let (v_16 : expression (bv 16)) <- eval (extract v_2 112 128);
      let (v_17 : expression (bv 16)) <- eval (extract v_4 112 128);
      let (v_18 : expression (bv 16)) <- eval (extract v_2 96 112);
      let (v_19 : expression (bv 16)) <- eval (extract v_4 96 112);
      let v_20 <- eval (concat (add (mul (sext v_12 32) (sext v_13 32)) (mul (sext v_14 32) (sext v_15 32))) (add (mul (sext v_16 32) (sext v_17 32)) (mul (sext v_18 32) (sext v_19 32))));
      let v_21 <- eval (concat (add (mul (sext v_8 32) (sext v_9 32)) (mul (sext v_10 32) (sext v_11 32))) v_20);
      let v_22 <- eval (concat (add (mul (sext v_3 32) (sext v_5 32)) (mul (sext v_6 32) (sext v_7 32))) v_21);
      setRegister (lhs.of_reg xmm_1) v_22;
      pure ()
     action
