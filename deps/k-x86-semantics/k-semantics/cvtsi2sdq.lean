def cvtsi2sdq : instruction :=
  definst "cvtsi2sdq" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 64)) <- eval (extract v_2 0 64);
      let v_4 <- evaluateAddress mem_0;
      let v_5 <- load v_4 8;
      let v_6 <- eval (concat v_3 (fp_bitcast_to_bv (int_convert_to_fp float_class.fp64 64 v_5) 64));
      setRegister (lhs.of_reg xmm_1) v_6;
      pure ()
     action;
    instr_pat $ fun (r64_0 : reg (bv 64)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 64)) <- eval (extract v_2 0 64);
      let v_4 <- getRegister (lhs.of_reg r64_0);
      let v_5 <- eval (concat v_3 (fp_bitcast_to_bv (int_convert_to_fp float_class.fp64 64 v_4) 64));
      setRegister (lhs.of_reg xmm_1) v_5;
      pure ()
     action
