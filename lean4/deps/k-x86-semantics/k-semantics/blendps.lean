def blendps1 : instruction :=
  definst "blendps" $ do
    pattern fun (v_3017 : imm int) (v_3015 : reg (bv 128)) (v_3016 : reg (bv 128)) => do
      v_5632 <- eval (handleImmediateWithSignExtend v_3017 8 8);
      v_5634 <- getRegister v_3016;
      v_5636 <- getRegister v_3015;
      setRegister (lhs.of_reg v_3016) (concat (mux (isBitClear v_5632 4) (extract v_5634 0 32) (extract v_5636 0 32)) (concat (mux (isBitClear v_5632 5) (extract v_5634 32 64) (extract v_5636 32 64)) (concat (mux (isBitClear v_5632 6) (extract v_5634 64 96) (extract v_5636 64 96)) (mux (isBitClear v_5632 7) (extract v_5634 96 128) (extract v_5636 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3011 : imm int) (v_3014 : Mem) (v_3010 : reg (bv 128)) => do
      v_9126 <- eval (handleImmediateWithSignExtend v_3011 8 8);
      v_9128 <- getRegister v_3010;
      v_9130 <- evaluateAddress v_3014;
      v_9131 <- load v_9130 16;
      setRegister (lhs.of_reg v_3010) (concat (mux (isBitClear v_9126 4) (extract v_9128 0 32) (extract v_9131 0 32)) (concat (mux (isBitClear v_9126 5) (extract v_9128 32 64) (extract v_9131 32 64)) (concat (mux (isBitClear v_9126 6) (extract v_9128 64 96) (extract v_9131 64 96)) (mux (isBitClear v_9126 7) (extract v_9128 96 128) (extract v_9131 96 128)))));
      pure ()
    pat_end
