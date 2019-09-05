def blendps1 : instruction :=
  definst "blendps" $ do
    pattern fun (v_2989 : imm int) (v_2992 : reg (bv 128)) (v_2993 : reg (bv 128)) => do
      v_5751 <- eval (handleImmediateWithSignExtend v_2989 8 8);
      v_5753 <- getRegister v_2993;
      v_5755 <- getRegister v_2992;
      setRegister (lhs.of_reg v_2993) (concat (mux (isBitClear v_5751 4) (extract v_5753 0 32) (extract v_5755 0 32)) (concat (mux (isBitClear v_5751 5) (extract v_5753 32 64) (extract v_5755 32 64)) (concat (mux (isBitClear v_5751 6) (extract v_5753 64 96) (extract v_5755 64 96)) (mux (isBitClear v_5751 7) (extract v_5753 96 128) (extract v_5755 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2984 : imm int) (v_2986 : Mem) (v_2987 : reg (bv 128)) => do
      v_9302 <- eval (handleImmediateWithSignExtend v_2984 8 8);
      v_9304 <- getRegister v_2987;
      v_9306 <- evaluateAddress v_2986;
      v_9307 <- load v_9306 16;
      setRegister (lhs.of_reg v_2987) (concat (mux (isBitClear v_9302 4) (extract v_9304 0 32) (extract v_9307 0 32)) (concat (mux (isBitClear v_9302 5) (extract v_9304 32 64) (extract v_9307 32 64)) (concat (mux (isBitClear v_9302 6) (extract v_9304 64 96) (extract v_9307 64 96)) (mux (isBitClear v_9302 7) (extract v_9304 96 128) (extract v_9307 96 128)))));
      pure ()
    pat_end
