def pblendw1 : instruction :=
  definst "pblendw" $ do
    pattern fun (v_3328 : imm int) (v_3329 : reg (bv 128)) (v_3330 : reg (bv 128)) => do
      v_6641 <- eval (handleImmediateWithSignExtend v_3328 8 8);
      v_6643 <- getRegister v_3330;
      v_6645 <- getRegister v_3329;
      setRegister (lhs.of_reg v_3330) (concat (mux (isBitClear v_6641 0) (extract v_6643 0 16) (extract v_6645 0 16)) (concat (mux (isBitClear v_6641 1) (extract v_6643 16 32) (extract v_6645 16 32)) (concat (mux (isBitClear v_6641 2) (extract v_6643 32 48) (extract v_6645 32 48)) (concat (mux (isBitClear v_6641 3) (extract v_6643 48 64) (extract v_6645 48 64)) (concat (mux (isBitClear v_6641 4) (extract v_6643 64 80) (extract v_6645 64 80)) (concat (mux (isBitClear v_6641 5) (extract v_6643 80 96) (extract v_6645 80 96)) (concat (mux (isBitClear v_6641 6) (extract v_6643 96 112) (extract v_6645 96 112)) (mux (isBitClear v_6641 7) (extract v_6643 112 128) (extract v_6645 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_3324 : imm int) (v_3323 : Mem) (v_3325 : reg (bv 128)) => do
      v_10532 <- eval (handleImmediateWithSignExtend v_3324 8 8);
      v_10534 <- getRegister v_3325;
      v_10536 <- evaluateAddress v_3323;
      v_10537 <- load v_10536 16;
      setRegister (lhs.of_reg v_3325) (concat (mux (isBitClear v_10532 0) (extract v_10534 0 16) (extract v_10537 0 16)) (concat (mux (isBitClear v_10532 1) (extract v_10534 16 32) (extract v_10537 16 32)) (concat (mux (isBitClear v_10532 2) (extract v_10534 32 48) (extract v_10537 32 48)) (concat (mux (isBitClear v_10532 3) (extract v_10534 48 64) (extract v_10537 48 64)) (concat (mux (isBitClear v_10532 4) (extract v_10534 64 80) (extract v_10537 64 80)) (concat (mux (isBitClear v_10532 5) (extract v_10534 80 96) (extract v_10537 80 96)) (concat (mux (isBitClear v_10532 6) (extract v_10534 96 112) (extract v_10537 96 112)) (mux (isBitClear v_10532 7) (extract v_10534 112 128) (extract v_10537 112 128)))))))));
      pure ()
    pat_end
