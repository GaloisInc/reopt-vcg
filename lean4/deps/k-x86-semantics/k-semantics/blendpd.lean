def blendpd1 : instruction :=
  definst "blendpd" $ do
    pattern fun (v_2978 : imm int) (v_2981 : reg (bv 128)) (v_2982 : reg (bv 128)) => do
      v_5733 <- eval (handleImmediateWithSignExtend v_2978 8 8);
      v_5735 <- getRegister v_2982;
      v_5737 <- getRegister v_2981;
      setRegister (lhs.of_reg v_2982) (concat (mux (isBitClear v_5733 6) (extract v_5735 0 64) (extract v_5737 0 64)) (mux (isBitClear v_5733 7) (extract v_5735 64 128) (extract v_5737 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2973 : imm int) (v_2975 : Mem) (v_2976 : reg (bv 128)) => do
      v_9288 <- eval (handleImmediateWithSignExtend v_2973 8 8);
      v_9290 <- getRegister v_2976;
      v_9292 <- evaluateAddress v_2975;
      v_9293 <- load v_9292 16;
      setRegister (lhs.of_reg v_2976) (concat (mux (isBitClear v_9288 6) (extract v_9290 0 64) (extract v_9293 0 64)) (mux (isBitClear v_9288 7) (extract v_9290 64 128) (extract v_9293 64 128)));
      pure ()
    pat_end
