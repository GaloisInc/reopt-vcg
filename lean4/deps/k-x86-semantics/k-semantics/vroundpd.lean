def vroundpd1 : instruction :=
  definst "vroundpd" $ do
    pattern fun (v_2897 : imm int) (v_2899 : reg (bv 128)) (v_2900 : reg (bv 128)) => do
      v_6670 <- getRegister v_2899;
      v_6672 <- eval (handleImmediateWithSignExtend v_2897 8 8);
      setRegister (lhs.of_reg v_2900) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_6670 0 64) v_6672) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_6670 64 128) v_6672));
      pure ()
    pat_end;
    pattern fun (v_2908 : imm int) (v_2910 : reg (bv 256)) (v_2911 : reg (bv 256)) => do
      v_6683 <- getRegister v_2910;
      v_6685 <- eval (handleImmediateWithSignExtend v_2908 8 8);
      setRegister (lhs.of_reg v_2911) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_6683 0 64) v_6685) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_6683 64 128) v_6685) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_6683 128 192) v_6685) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_6683 192 256) v_6685))));
      pure ()
    pat_end;
    pattern fun (v_2892 : imm int) (v_2893 : Mem) (v_2894 : reg (bv 128)) => do
      v_12677 <- evaluateAddress v_2893;
      v_12678 <- load v_12677 16;
      v_12680 <- eval (handleImmediateWithSignExtend v_2892 8 8);
      setRegister (lhs.of_reg v_2894) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_12678 0 64) v_12680) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_12678 64 128) v_12680));
      pure ()
    pat_end;
    pattern fun (v_2903 : imm int) (v_2904 : Mem) (v_2905 : reg (bv 256)) => do
      v_12686 <- evaluateAddress v_2904;
      v_12687 <- load v_12686 32;
      v_12689 <- eval (handleImmediateWithSignExtend v_2903 8 8);
      setRegister (lhs.of_reg v_2905) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_12687 0 64) v_12689) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_12687 64 128) v_12689) (concat (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_12687 128 192) v_12689) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_double_to_int64_rm (extract v_12687 192 256) v_12689))));
      pure ()
    pat_end
