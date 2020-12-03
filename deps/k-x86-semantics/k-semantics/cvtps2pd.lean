def cvtps2pd : instruction :=
  definst "cvtps2pd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 8;
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- eval (bv_bitcast_to_fp float_class.fp32 v_4);
      let (v_6 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_7 <- eval (bv_bitcast_to_fp float_class.fp32 v_6);
      let v_8 <- eval (concat (fp_bitcast_to_bv (fp_round v_5 53 11) 64) (fp_bitcast_to_bv (fp_round v_7 53 11) 64));
      setRegister (lhs.of_reg xmm_1) v_8;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 64 96);
      let v_4 <- eval (bv_bitcast_to_fp float_class.fp32 v_3);
      let (v_5 : expression (bv 32)) <- eval (extract v_2 96 128);
      let v_6 <- eval (bv_bitcast_to_fp float_class.fp32 v_5);
      let v_7 <- eval (concat (fp_bitcast_to_bv (fp_round v_4 53 11) 64) (fp_bitcast_to_bv (fp_round v_6 53 11) 64));
      setRegister (lhs.of_reg xmm_1) v_7;
      pure ()
     action
