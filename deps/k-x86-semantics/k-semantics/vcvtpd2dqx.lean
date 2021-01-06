def vcvtpd2dqx : instruction :=
  definst "vcvtpd2dqx" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let (v_5 : expression (bv 64)) <- eval (extract v_3 64 128);
      let v_6 <- eval (concat (/- (_) -/ cvt_double_to_int32_truncate v_4) (/- (_) -/ cvt_double_to_int32_truncate v_5));
      let v_7 <- eval (concat (expression.bv_nat 64 0) v_6);
      setRegister (lhs.of_reg xmm_1) v_7;
      pure ()
     action
