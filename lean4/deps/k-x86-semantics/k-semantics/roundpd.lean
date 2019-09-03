def roundpd1 : instruction :=
  definst "roundpd" $ do
    pattern fun (v_2807 : imm int) (v_2810 : reg (bv 128)) (v_2811 : reg (bv 128)) => do
      v_5755 <- getRegister v_2810;
      v_5757 <- eval (handleImmediateWithSignExtend v_2807 8 8);
      setRegister (lhs.of_reg v_2811) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_5755 0 64) v_5757) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_5755 64 128) v_5757));
      pure ()
    pat_end;
    pattern fun (v_2802 : imm int) (v_2803 : Mem) (v_2806 : reg (bv 128)) => do
      v_12952 <- evaluateAddress v_2803;
      v_12953 <- load v_12952 16;
      v_12955 <- eval (handleImmediateWithSignExtend v_2802 8 8);
      setRegister (lhs.of_reg v_2806) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_12953 0 64) v_12955) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_12953 64 128) v_12955));
      pure ()
    pat_end
