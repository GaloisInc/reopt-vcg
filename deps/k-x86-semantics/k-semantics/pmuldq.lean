def pmuldq : instruction :=
  definst "pmuldq" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 32 64);
      let v_4 <- evaluateAddress mem_0;
      let v_5 <- load v_4 16;
      let (v_6 : expression (bv 32)) <- eval (extract v_5 32 64);
      let (v_7 : expression (bv 32)) <- eval (extract v_2 96 128);
      let (v_8 : expression (bv 32)) <- eval (extract v_5 96 128);
      let v_9 <- eval (concat (mul (sext v_3 64) (sext v_6 64)) (mul (sext v_7 64) (sext v_8 64)));
      setRegister (lhs.of_reg xmm_1) v_9;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 32 64);
      let v_4 <- getRegister (lhs.of_reg xmm_0);
      let (v_5 : expression (bv 32)) <- eval (extract v_4 32 64);
      let (v_6 : expression (bv 32)) <- eval (extract v_2 96 128);
      let (v_7 : expression (bv 32)) <- eval (extract v_4 96 128);
      let v_8 <- eval (concat (mul (sext v_3 64) (sext v_5 64)) (mul (sext v_6 64) (sext v_7 64)));
      setRegister (lhs.of_reg xmm_1) v_8;
      pure ()
     action
