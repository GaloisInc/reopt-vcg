def vcvttsd2si1 : instruction :=
  definst "vcvttsd2si" $ do
    pattern fun (mem_0 : Mem) (r32_1 : reg (bv 32)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 8;
      setRegister (lhs.of_reg r32_1) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate v_3);
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (r64_1 : reg (bv 64)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 8;
      setRegister (lhs.of_reg r64_1) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate v_3);
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister xmm_0;
      setRegister (lhs.of_reg r32_1) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_2 64 128));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister xmm_0;
      setRegister (lhs.of_reg r64_1) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate (extract v_2 64 128));
      pure ()
    pat_end
