def vcvtsd2si1 : instruction :=
  definst "vcvtsd2si" $ do
    pattern fun (v_3238 : reg (bv 128)) (v_3237 : reg (bv 32)) => do
      v_6148 <- getRegister v_3238;
      setRegister (lhs.of_reg v_3237) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate (extract v_6148 64 128));
      pure ()
    pat_end;
    pattern fun (v_3247 : reg (bv 128)) (v_3243 : reg (bv 64)) => do
      v_6156 <- getRegister v_3247;
      setRegister (lhs.of_reg v_3243) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate (extract v_6156 64 128));
      pure ()
    pat_end;
    pattern fun (v_3230 : Mem) (v_3233 : reg (bv 32)) => do
      v_10214 <- evaluateAddress v_3230;
      v_10215 <- load v_10214 8;
      setRegister (lhs.of_reg v_3233) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int32_truncate v_10215);
      pure ()
    pat_end;
    pattern fun (v_3239 : Mem) (v_3240 : reg (bv 64)) => do
      v_10218 <- evaluateAddress v_3239;
      v_10219 <- load v_10218 8;
      setRegister (lhs.of_reg v_3240) (_(_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_truncate v_10219);
      pure ()
    pat_end
