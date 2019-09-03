def vpunpcklwd1 : instruction :=
  definst "vpunpcklwd" $ do
    pattern fun (v_2744 : reg (bv 128)) (v_2745 : reg (bv 128)) (v_2746 : reg (bv 128)) => do
      v_6430 <- getRegister v_2744;
      v_6432 <- getRegister v_2745;
      setRegister (lhs.of_reg v_2746) (concat (concat (extract v_6430 64 80) (extract v_6432 64 80)) (concat (concat (extract v_6430 80 96) (extract v_6432 80 96)) (concat (concat (extract v_6430 96 112) (extract v_6432 96 112)) (concat (extract v_6430 112 128) (extract v_6432 112 128)))));
      pure ()
    pat_end;
    pattern fun (v_2755 : reg (bv 256)) (v_2756 : reg (bv 256)) (v_2757 : reg (bv 256)) => do
      v_6453 <- getRegister v_2755;
      v_6455 <- getRegister v_2756;
      setRegister (lhs.of_reg v_2757) (concat (concat (extract v_6453 64 80) (extract v_6455 64 80)) (concat (concat (extract v_6453 80 96) (extract v_6455 80 96)) (concat (concat (extract v_6453 96 112) (extract v_6455 96 112)) (concat (concat (extract v_6453 112 128) (extract v_6455 112 128)) (concat (concat (extract v_6453 192 208) (extract v_6455 192 208)) (concat (concat (extract v_6453 208 224) (extract v_6455 208 224)) (concat (concat (extract v_6453 224 240) (extract v_6455 224 240)) (concat (extract v_6453 240 256) (extract v_6455 240 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_2739 : Mem) (v_2740 : reg (bv 128)) (v_2741 : reg (bv 128)) => do
      v_12837 <- evaluateAddress v_2739;
      v_12838 <- load v_12837 16;
      v_12840 <- getRegister v_2740;
      setRegister (lhs.of_reg v_2741) (concat (concat (extract v_12838 64 80) (extract v_12840 64 80)) (concat (concat (extract v_12838 80 96) (extract v_12840 80 96)) (concat (concat (extract v_12838 96 112) (extract v_12840 96 112)) (concat (extract v_12838 112 128) (extract v_12840 112 128)))));
      pure ()
    pat_end;
    pattern fun (v_2750 : Mem) (v_2751 : reg (bv 256)) (v_2752 : reg (bv 256)) => do
      v_12856 <- evaluateAddress v_2750;
      v_12857 <- load v_12856 32;
      v_12859 <- getRegister v_2751;
      setRegister (lhs.of_reg v_2752) (concat (concat (extract v_12857 64 80) (extract v_12859 64 80)) (concat (concat (extract v_12857 80 96) (extract v_12859 80 96)) (concat (concat (extract v_12857 96 112) (extract v_12859 96 112)) (concat (concat (extract v_12857 112 128) (extract v_12859 112 128)) (concat (concat (extract v_12857 192 208) (extract v_12859 192 208)) (concat (concat (extract v_12857 208 224) (extract v_12859 208 224)) (concat (concat (extract v_12857 224 240) (extract v_12859 224 240)) (concat (extract v_12857 240 256) (extract v_12859 240 256)))))))));
      pure ()
    pat_end
