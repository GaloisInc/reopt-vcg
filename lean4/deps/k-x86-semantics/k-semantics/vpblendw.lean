def vpblendw1 : instruction :=
  definst "vpblendw" $ do
    pattern fun (v_2753 : imm int) (v_2754 : reg (bv 128)) (v_2755 : reg (bv 128)) (v_2756 : reg (bv 128)) => do
      v_6787 <- eval (handleImmediateWithSignExtend v_2753 8 8);
      v_6789 <- getRegister v_2755;
      v_6791 <- getRegister v_2754;
      setRegister (lhs.of_reg v_2756) (concat (mux (isBitClear v_6787 0) (extract v_6789 0 16) (extract v_6791 0 16)) (concat (mux (isBitClear v_6787 1) (extract v_6789 16 32) (extract v_6791 16 32)) (concat (mux (isBitClear v_6787 2) (extract v_6789 32 48) (extract v_6791 32 48)) (concat (mux (isBitClear v_6787 3) (extract v_6789 48 64) (extract v_6791 48 64)) (concat (mux (isBitClear v_6787 4) (extract v_6789 64 80) (extract v_6791 64 80)) (concat (mux (isBitClear v_6787 5) (extract v_6789 80 96) (extract v_6791 80 96)) (concat (mux (isBitClear v_6787 6) (extract v_6789 96 112) (extract v_6791 96 112)) (mux (isBitClear v_6787 7) (extract v_6789 112 128) (extract v_6791 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2766 : imm int) (v_2767 : reg (bv 256)) (v_2768 : reg (bv 256)) (v_2769 : reg (bv 256)) => do
      v_6836 <- eval (handleImmediateWithSignExtend v_2766 8 8);
      v_6837 <- eval (isBitClear v_6836 0);
      v_6838 <- getRegister v_2768;
      v_6840 <- getRegister v_2767;
      v_6843 <- eval (isBitClear v_6836 1);
      v_6847 <- eval (isBitClear v_6836 2);
      v_6851 <- eval (isBitClear v_6836 3);
      v_6855 <- eval (isBitClear v_6836 4);
      v_6859 <- eval (isBitClear v_6836 5);
      v_6863 <- eval (isBitClear v_6836 6);
      v_6867 <- eval (isBitClear v_6836 7);
      setRegister (lhs.of_reg v_2769) (concat (mux v_6837 (extract v_6838 0 16) (extract v_6840 0 16)) (concat (mux v_6843 (extract v_6838 16 32) (extract v_6840 16 32)) (concat (mux v_6847 (extract v_6838 32 48) (extract v_6840 32 48)) (concat (mux v_6851 (extract v_6838 48 64) (extract v_6840 48 64)) (concat (mux v_6855 (extract v_6838 64 80) (extract v_6840 64 80)) (concat (mux v_6859 (extract v_6838 80 96) (extract v_6840 80 96)) (concat (mux v_6863 (extract v_6838 96 112) (extract v_6840 96 112)) (concat (mux v_6867 (extract v_6838 112 128) (extract v_6840 112 128)) (concat (mux v_6837 (extract v_6838 128 144) (extract v_6840 128 144)) (concat (mux v_6843 (extract v_6838 144 160) (extract v_6840 144 160)) (concat (mux v_6847 (extract v_6838 160 176) (extract v_6840 160 176)) (concat (mux v_6851 (extract v_6838 176 192) (extract v_6840 176 192)) (concat (mux v_6855 (extract v_6838 192 208) (extract v_6840 192 208)) (concat (mux v_6859 (extract v_6838 208 224) (extract v_6840 208 224)) (concat (mux v_6863 (extract v_6838 224 240) (extract v_6840 224 240)) (mux v_6867 (extract v_6838 240 256) (extract v_6840 240 256)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2748 : imm int) (v_2747 : Mem) (v_2749 : reg (bv 128)) (v_2750 : reg (bv 128)) => do
      v_15444 <- eval (handleImmediateWithSignExtend v_2748 8 8);
      v_15446 <- getRegister v_2749;
      v_15448 <- evaluateAddress v_2747;
      v_15449 <- load v_15448 16;
      setRegister (lhs.of_reg v_2750) (concat (mux (isBitClear v_15444 0) (extract v_15446 0 16) (extract v_15449 0 16)) (concat (mux (isBitClear v_15444 1) (extract v_15446 16 32) (extract v_15449 16 32)) (concat (mux (isBitClear v_15444 2) (extract v_15446 32 48) (extract v_15449 32 48)) (concat (mux (isBitClear v_15444 3) (extract v_15446 48 64) (extract v_15449 48 64)) (concat (mux (isBitClear v_15444 4) (extract v_15446 64 80) (extract v_15449 64 80)) (concat (mux (isBitClear v_15444 5) (extract v_15446 80 96) (extract v_15449 80 96)) (concat (mux (isBitClear v_15444 6) (extract v_15446 96 112) (extract v_15449 96 112)) (mux (isBitClear v_15444 7) (extract v_15446 112 128) (extract v_15449 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2761 : imm int) (v_2760 : Mem) (v_2762 : reg (bv 256)) (v_2763 : reg (bv 256)) => do
      v_15488 <- eval (handleImmediateWithSignExtend v_2761 8 8);
      v_15489 <- eval (isBitClear v_15488 0);
      v_15490 <- getRegister v_2762;
      v_15492 <- evaluateAddress v_2760;
      v_15493 <- load v_15492 32;
      v_15496 <- eval (isBitClear v_15488 1);
      v_15500 <- eval (isBitClear v_15488 2);
      v_15504 <- eval (isBitClear v_15488 3);
      v_15508 <- eval (isBitClear v_15488 4);
      v_15512 <- eval (isBitClear v_15488 5);
      v_15516 <- eval (isBitClear v_15488 6);
      v_15520 <- eval (isBitClear v_15488 7);
      setRegister (lhs.of_reg v_2763) (concat (mux v_15489 (extract v_15490 0 16) (extract v_15493 0 16)) (concat (mux v_15496 (extract v_15490 16 32) (extract v_15493 16 32)) (concat (mux v_15500 (extract v_15490 32 48) (extract v_15493 32 48)) (concat (mux v_15504 (extract v_15490 48 64) (extract v_15493 48 64)) (concat (mux v_15508 (extract v_15490 64 80) (extract v_15493 64 80)) (concat (mux v_15512 (extract v_15490 80 96) (extract v_15493 80 96)) (concat (mux v_15516 (extract v_15490 96 112) (extract v_15493 96 112)) (concat (mux v_15520 (extract v_15490 112 128) (extract v_15493 112 128)) (concat (mux v_15489 (extract v_15490 128 144) (extract v_15493 128 144)) (concat (mux v_15496 (extract v_15490 144 160) (extract v_15493 144 160)) (concat (mux v_15500 (extract v_15490 160 176) (extract v_15493 160 176)) (concat (mux v_15504 (extract v_15490 176 192) (extract v_15493 176 192)) (concat (mux v_15508 (extract v_15490 192 208) (extract v_15493 192 208)) (concat (mux v_15512 (extract v_15490 208 224) (extract v_15493 208 224)) (concat (mux v_15516 (extract v_15490 224 240) (extract v_15493 224 240)) (mux v_15520 (extract v_15490 240 256) (extract v_15493 240 256)))))))))))))))));
      pure ()
    pat_end
