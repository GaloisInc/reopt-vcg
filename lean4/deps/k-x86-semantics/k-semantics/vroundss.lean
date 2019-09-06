def vroundss1 : instruction :=
  definst "vroundss" $ do
    pattern fun (v_2955 : imm int) (v_2957 : reg (bv 128)) (v_2958 : reg (bv 128)) (v_2959 : reg (bv 128)) => do
      v_6767 <- getRegister v_2958;
      v_6769 <- getRegister v_2957;
      setRegister (lhs.of_reg v_2959) (concat (extract v_6767 0 96) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm (extract v_6769 96 128) (handleImmediateWithSignExtend v_2955 8 8)));
      pure ()
    pat_end;
    pattern fun (v_2949 : imm int) (v_2950 : Mem) (v_2951 : reg (bv 128)) (v_2952 : reg (bv 128)) => do
      v_12751 <- getRegister v_2951;
      v_12753 <- evaluateAddress v_2950;
      v_12754 <- load v_12753 4;
      setRegister (lhs.of_reg v_2952) (concat (extract v_12751 0 96) (_(_,_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_rm v_12754 (handleImmediateWithSignExtend v_2949 8 8)));
      pure ()
    pat_end
