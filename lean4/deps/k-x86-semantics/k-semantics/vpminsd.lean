def vpminsd1 : instruction :=
  definst "vpminsd" $ do
    pattern fun (v_2473 : reg (bv 128)) (v_2474 : reg (bv 128)) (v_2475 : reg (bv 128)) => do
      v_4623 <- getRegister v_2474;
      v_4624 <- eval (extract v_4623 0 32);
      v_4625 <- getRegister v_2473;
      v_4626 <- eval (extract v_4625 0 32);
      v_4629 <- eval (extract v_4623 32 64);
      v_4630 <- eval (extract v_4625 32 64);
      v_4633 <- eval (extract v_4623 64 96);
      v_4634 <- eval (extract v_4625 64 96);
      v_4637 <- eval (extract v_4623 96 128);
      v_4638 <- eval (extract v_4625 96 128);
      setRegister (lhs.of_reg v_2475) (concat (mux (slt v_4624 v_4626) v_4624 v_4626) (concat (mux (slt v_4629 v_4630) v_4629 v_4630) (concat (mux (slt v_4633 v_4634) v_4633 v_4634) (mux (slt v_4637 v_4638) v_4637 v_4638))));
      pure ()
    pat_end;
    pattern fun (v_2484 : reg (bv 256)) (v_2485 : reg (bv 256)) (v_2486 : reg (bv 256)) => do
      v_4650 <- getRegister v_2485;
      v_4651 <- eval (extract v_4650 0 32);
      v_4652 <- getRegister v_2484;
      v_4653 <- eval (extract v_4652 0 32);
      v_4656 <- eval (extract v_4650 32 64);
      v_4657 <- eval (extract v_4652 32 64);
      v_4660 <- eval (extract v_4650 64 96);
      v_4661 <- eval (extract v_4652 64 96);
      v_4664 <- eval (extract v_4650 96 128);
      v_4665 <- eval (extract v_4652 96 128);
      v_4668 <- eval (extract v_4650 128 160);
      v_4669 <- eval (extract v_4652 128 160);
      v_4672 <- eval (extract v_4650 160 192);
      v_4673 <- eval (extract v_4652 160 192);
      v_4676 <- eval (extract v_4650 192 224);
      v_4677 <- eval (extract v_4652 192 224);
      v_4680 <- eval (extract v_4650 224 256);
      v_4681 <- eval (extract v_4652 224 256);
      setRegister (lhs.of_reg v_2486) (concat (mux (slt v_4651 v_4653) v_4651 v_4653) (concat (mux (slt v_4656 v_4657) v_4656 v_4657) (concat (mux (slt v_4660 v_4661) v_4660 v_4661) (concat (mux (slt v_4664 v_4665) v_4664 v_4665) (concat (mux (slt v_4668 v_4669) v_4668 v_4669) (concat (mux (slt v_4672 v_4673) v_4672 v_4673) (concat (mux (slt v_4676 v_4677) v_4676 v_4677) (mux (slt v_4680 v_4681) v_4680 v_4681))))))));
      pure ()
    pat_end;
    pattern fun (v_2470 : Mem) (v_2468 : reg (bv 128)) (v_2469 : reg (bv 128)) => do
      v_12035 <- getRegister v_2468;
      v_12036 <- eval (extract v_12035 0 32);
      v_12037 <- evaluateAddress v_2470;
      v_12038 <- load v_12037 16;
      v_12039 <- eval (extract v_12038 0 32);
      v_12042 <- eval (extract v_12035 32 64);
      v_12043 <- eval (extract v_12038 32 64);
      v_12046 <- eval (extract v_12035 64 96);
      v_12047 <- eval (extract v_12038 64 96);
      v_12050 <- eval (extract v_12035 96 128);
      v_12051 <- eval (extract v_12038 96 128);
      setRegister (lhs.of_reg v_2469) (concat (mux (slt v_12036 v_12039) v_12036 v_12039) (concat (mux (slt v_12042 v_12043) v_12042 v_12043) (concat (mux (slt v_12046 v_12047) v_12046 v_12047) (mux (slt v_12050 v_12051) v_12050 v_12051))));
      pure ()
    pat_end;
    pattern fun (v_2479 : Mem) (v_2480 : reg (bv 256)) (v_2481 : reg (bv 256)) => do
      v_12058 <- getRegister v_2480;
      v_12059 <- eval (extract v_12058 0 32);
      v_12060 <- evaluateAddress v_2479;
      v_12061 <- load v_12060 32;
      v_12062 <- eval (extract v_12061 0 32);
      v_12065 <- eval (extract v_12058 32 64);
      v_12066 <- eval (extract v_12061 32 64);
      v_12069 <- eval (extract v_12058 64 96);
      v_12070 <- eval (extract v_12061 64 96);
      v_12073 <- eval (extract v_12058 96 128);
      v_12074 <- eval (extract v_12061 96 128);
      v_12077 <- eval (extract v_12058 128 160);
      v_12078 <- eval (extract v_12061 128 160);
      v_12081 <- eval (extract v_12058 160 192);
      v_12082 <- eval (extract v_12061 160 192);
      v_12085 <- eval (extract v_12058 192 224);
      v_12086 <- eval (extract v_12061 192 224);
      v_12089 <- eval (extract v_12058 224 256);
      v_12090 <- eval (extract v_12061 224 256);
      setRegister (lhs.of_reg v_2481) (concat (mux (slt v_12059 v_12062) v_12059 v_12062) (concat (mux (slt v_12065 v_12066) v_12065 v_12066) (concat (mux (slt v_12069 v_12070) v_12069 v_12070) (concat (mux (slt v_12073 v_12074) v_12073 v_12074) (concat (mux (slt v_12077 v_12078) v_12077 v_12078) (concat (mux (slt v_12081 v_12082) v_12081 v_12082) (concat (mux (slt v_12085 v_12086) v_12085 v_12086) (mux (slt v_12089 v_12090) v_12089 v_12090))))))));
      pure ()
    pat_end
