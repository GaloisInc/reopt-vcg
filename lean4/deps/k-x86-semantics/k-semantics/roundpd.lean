def roundpd1 : instruction :=
  definst "roundpd" $ do
    pattern fun (v_2898 : imm int) (v_2901 : reg (bv 128)) (v_2902 : reg (bv 128)) => do
      v_5205 <- getRegister v_2901;
      v_5207 <- eval (handleImmediateWithSignExtend v_2898 8 8);
      setRegister (lhs.of_reg v_2902) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_5205 0 64) v_5207) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_5205 64 128) v_5207));
      pure ()
    pat_end;
    pattern fun (v_2893 : imm int) (v_2894 : Mem) (v_2897 : reg (bv 128)) => do
      v_10515 <- evaluateAddress v_2894;
      v_10516 <- load v_10515 16;
      v_10518 <- eval (handleImmediateWithSignExtend v_2893 8 8);
      setRegister (lhs.of_reg v_2897) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_10516 0 64) v_10518) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_10516 64 128) v_10518));
      pure ()
    pat_end
