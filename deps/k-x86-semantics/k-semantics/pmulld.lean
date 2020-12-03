def pmulld : instruction :=
  definst "pmulld" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      let v_4 <- evaluateAddress mem_0;
      let v_5 <- load v_4 16;
      let (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      let (v_7 : expression (bv 32)) <- eval (extract (mul (sext v_3 64) (sext v_6 64)) 32 64);
      let (v_8 : expression (bv 32)) <- eval (extract v_2 32 64);
      let (v_9 : expression (bv 32)) <- eval (extract v_5 32 64);
      let (v_10 : expression (bv 32)) <- eval (extract (mul (sext v_8 64) (sext v_9 64)) 32 64);
      let (v_11 : expression (bv 32)) <- eval (extract v_2 64 96);
      let (v_12 : expression (bv 32)) <- eval (extract v_5 64 96);
      let (v_13 : expression (bv 32)) <- eval (extract (mul (sext v_11 64) (sext v_12 64)) 32 64);
      let (v_14 : expression (bv 32)) <- eval (extract v_2 96 128);
      let (v_15 : expression (bv 32)) <- eval (extract v_5 96 128);
      let (v_16 : expression (bv 32)) <- eval (extract (mul (sext v_14 64) (sext v_15 64)) 32 64);
      let v_17 <- eval (concat v_13 v_16);
      let v_18 <- eval (concat v_10 v_17);
      let v_19 <- eval (concat v_7 v_18);
      setRegister (lhs.of_reg xmm_1) v_19;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      let v_4 <- getRegister (lhs.of_reg xmm_0);
      let (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      let (v_6 : expression (bv 32)) <- eval (extract (mul (sext v_3 64) (sext v_5 64)) 32 64);
      let (v_7 : expression (bv 32)) <- eval (extract v_2 32 64);
      let (v_8 : expression (bv 32)) <- eval (extract v_4 32 64);
      let (v_9 : expression (bv 32)) <- eval (extract (mul (sext v_7 64) (sext v_8 64)) 32 64);
      let (v_10 : expression (bv 32)) <- eval (extract v_2 64 96);
      let (v_11 : expression (bv 32)) <- eval (extract v_4 64 96);
      let (v_12 : expression (bv 32)) <- eval (extract (mul (sext v_10 64) (sext v_11 64)) 32 64);
      let (v_13 : expression (bv 32)) <- eval (extract v_2 96 128);
      let (v_14 : expression (bv 32)) <- eval (extract v_4 96 128);
      let (v_15 : expression (bv 32)) <- eval (extract (mul (sext v_13 64) (sext v_14 64)) 32 64);
      let v_16 <- eval (concat v_12 v_15);
      let v_17 <- eval (concat v_9 v_16);
      let v_18 <- eval (concat v_6 v_17);
      setRegister (lhs.of_reg xmm_1) v_18;
      pure ()
     action
