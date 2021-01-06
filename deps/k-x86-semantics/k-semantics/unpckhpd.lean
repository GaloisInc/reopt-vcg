def unpckhpd : instruction :=
  definst "unpckhpd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      let v_7 <- eval (concat v_4 v_6);
      setRegister (lhs.of_reg xmm_1) v_7;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 64)) <- eval (extract v_2 0 64);
      let v_4 <- getRegister (lhs.of_reg xmm_1);
      let (v_5 : expression (bv 64)) <- eval (extract v_4 0 64);
      let v_6 <- eval (concat v_3 v_5);
      setRegister (lhs.of_reg xmm_1) v_6;
      pure ()
     action
