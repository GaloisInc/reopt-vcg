def pblendw1 : instruction :=
  definst "pblendw" $ do
    pattern fun (v_3302 : imm int) (v_3304 : reg (bv 128)) (v_3305 : reg (bv 128)) => do
      v_6614 <- eval (handleImmediateWithSignExtend v_3302 8 8);
      v_6616 <- getRegister v_3305;
      v_6618 <- getRegister v_3304;
      setRegister (lhs.of_reg v_3305) (concat (mux (isBitClear v_6614 0) (extract v_6616 0 16) (extract v_6618 0 16)) (concat (mux (isBitClear v_6614 1) (extract v_6616 16 32) (extract v_6618 16 32)) (concat (mux (isBitClear v_6614 2) (extract v_6616 32 48) (extract v_6618 32 48)) (concat (mux (isBitClear v_6614 3) (extract v_6616 48 64) (extract v_6618 48 64)) (concat (mux (isBitClear v_6614 4) (extract v_6616 64 80) (extract v_6618 64 80)) (concat (mux (isBitClear v_6614 5) (extract v_6616 80 96) (extract v_6618 80 96)) (concat (mux (isBitClear v_6614 6) (extract v_6616 96 112) (extract v_6618 96 112)) (mux (isBitClear v_6614 7) (extract v_6616 112 128) (extract v_6618 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_3297 : imm int) (v_3298 : Mem) (v_3299 : reg (bv 128)) => do
      v_10505 <- eval (handleImmediateWithSignExtend v_3297 8 8);
      v_10507 <- getRegister v_3299;
      v_10509 <- evaluateAddress v_3298;
      v_10510 <- load v_10509 16;
      setRegister (lhs.of_reg v_3299) (concat (mux (isBitClear v_10505 0) (extract v_10507 0 16) (extract v_10510 0 16)) (concat (mux (isBitClear v_10505 1) (extract v_10507 16 32) (extract v_10510 16 32)) (concat (mux (isBitClear v_10505 2) (extract v_10507 32 48) (extract v_10510 32 48)) (concat (mux (isBitClear v_10505 3) (extract v_10507 48 64) (extract v_10510 48 64)) (concat (mux (isBitClear v_10505 4) (extract v_10507 64 80) (extract v_10510 64 80)) (concat (mux (isBitClear v_10505 5) (extract v_10507 80 96) (extract v_10510 80 96)) (concat (mux (isBitClear v_10505 6) (extract v_10507 96 112) (extract v_10510 96 112)) (mux (isBitClear v_10505 7) (extract v_10507 112 128) (extract v_10510 112 128)))))))));
      pure ()
    pat_end
