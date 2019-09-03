def vpunpcklwd1 : instruction :=
  definst "vpunpcklwd" $ do
    pattern fun (v_2734 : reg (bv 128)) (v_2735 : reg (bv 128)) (v_2736 : reg (bv 128)) => do
      v_6565 <- getRegister v_2734;
      v_6567 <- getRegister v_2735;
      setRegister (lhs.of_reg v_2736) (concat (concat (extract v_6565 64 80) (extract v_6567 64 80)) (concat (concat (extract v_6565 80 96) (extract v_6567 80 96)) (concat (concat (extract v_6565 96 112) (extract v_6567 96 112)) (concat (extract v_6565 112 128) (extract v_6567 112 128)))));
      pure ()
    pat_end;
    pattern fun (v_2744 : reg (bv 256)) (v_2745 : reg (bv 256)) (v_2746 : reg (bv 256)) => do
      v_6588 <- getRegister v_2744;
      v_6590 <- getRegister v_2745;
      setRegister (lhs.of_reg v_2746) (concat (concat (extract v_6588 64 80) (extract v_6590 64 80)) (concat (concat (extract v_6588 80 96) (extract v_6590 80 96)) (concat (concat (extract v_6588 96 112) (extract v_6590 96 112)) (concat (concat (extract v_6588 112 128) (extract v_6590 112 128)) (concat (concat (extract v_6588 192 208) (extract v_6590 192 208)) (concat (concat (extract v_6588 208 224) (extract v_6590 208 224)) (concat (concat (extract v_6588 224 240) (extract v_6590 224 240)) (concat (extract v_6588 240 256) (extract v_6590 240 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_2728 : Mem) (v_2729 : reg (bv 128)) (v_2730 : reg (bv 128)) => do
      v_12840 <- evaluateAddress v_2728;
      v_12841 <- load v_12840 16;
      v_12843 <- getRegister v_2729;
      setRegister (lhs.of_reg v_2730) (concat (concat (extract v_12841 64 80) (extract v_12843 64 80)) (concat (concat (extract v_12841 80 96) (extract v_12843 80 96)) (concat (concat (extract v_12841 96 112) (extract v_12843 96 112)) (concat (extract v_12841 112 128) (extract v_12843 112 128)))));
      pure ()
    pat_end;
    pattern fun (v_2739 : Mem) (v_2740 : reg (bv 256)) (v_2741 : reg (bv 256)) => do
      v_12859 <- evaluateAddress v_2739;
      v_12860 <- load v_12859 32;
      v_12862 <- getRegister v_2740;
      setRegister (lhs.of_reg v_2741) (concat (concat (extract v_12860 64 80) (extract v_12862 64 80)) (concat (concat (extract v_12860 80 96) (extract v_12862 80 96)) (concat (concat (extract v_12860 96 112) (extract v_12862 96 112)) (concat (concat (extract v_12860 112 128) (extract v_12862 112 128)) (concat (concat (extract v_12860 192 208) (extract v_12862 192 208)) (concat (concat (extract v_12860 208 224) (extract v_12862 208 224)) (concat (concat (extract v_12860 224 240) (extract v_12862 224 240)) (concat (extract v_12860 240 256) (extract v_12862 240 256)))))))));
      pure ()
    pat_end
