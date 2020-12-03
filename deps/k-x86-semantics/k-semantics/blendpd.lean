def blendpd : instruction :=
  definst "blendpd" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_4 <- getRegister (lhs.of_reg xmm_2);
      let (v_5 : expression (bv 64)) <- eval (extract v_4 0 64);
      let v_6 <- evaluateAddress mem_1;
      let v_7 <- load v_6 16;
      let (v_8 : expression (bv 64)) <- eval (extract v_7 0 64);
      let (v_9 : expression (bv 64)) <- eval (extract v_4 64 128);
      let (v_10 : expression (bv 64)) <- eval (extract v_7 64 128);
      let v_11 <- eval (concat (mux (isBitClear v_3 6) v_5 v_8) (mux (isBitClear v_3 7) v_9 v_10));
      setRegister (lhs.of_reg xmm_2) v_11;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_4 <- getRegister (lhs.of_reg xmm_2);
      let (v_5 : expression (bv 64)) <- eval (extract v_4 0 64);
      let v_6 <- getRegister (lhs.of_reg xmm_1);
      let (v_7 : expression (bv 64)) <- eval (extract v_6 0 64);
      let (v_8 : expression (bv 64)) <- eval (extract v_4 64 128);
      let (v_9 : expression (bv 64)) <- eval (extract v_6 64 128);
      let v_10 <- eval (concat (mux (isBitClear v_3 6) v_5 v_7) (mux (isBitClear v_3 7) v_8 v_9));
      setRegister (lhs.of_reg xmm_2) v_10;
      pure ()
     action
