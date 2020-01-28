def vfmsub213ss : instruction :=
  definst "vfmsub213ss" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 96 128));
      v_6 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 96 128));
      v_7 <- evaluateAddress mem_0;
      v_8 <- load v_7 4;
      v_9 <- eval (bv_bitcast_to_fp float_class.fp32 v_8);
      setRegister (lhs.of_reg xmm_2) (concat (extract v_3 0 96) (fp_bitcast_to_bv (fp_sub (fp_mul v_5 v_6) v_9) 32));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 96 128));
      v_6 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 96 128));
      v_7 <- getRegister (lhs.of_reg xmm_0);
      v_8 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_7 96 128));
      setRegister (lhs.of_reg xmm_2) (concat (extract v_3 0 96) (fp_bitcast_to_bv (fp_sub (fp_mul v_5 v_6) v_8) 32));
      pure ()
    pat_end
