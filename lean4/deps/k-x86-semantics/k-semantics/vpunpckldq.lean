def vpunpckldq1 : instruction :=
  definst "vpunpckldq" $ do
    pattern fun (v_2690 : reg (bv 128)) (v_2691 : reg (bv 128)) (v_2692 : reg (bv 128)) => do
      v_6501 <- getRegister v_2690;
      v_6503 <- getRegister v_2691;
      setRegister (lhs.of_reg v_2692) (concat (concat (extract v_6501 64 96) (extract v_6503 64 96)) (concat (extract v_6501 96 128) (extract v_6503 96 128)));
      pure ()
    pat_end;
    pattern fun (v_2700 : reg (bv 256)) (v_2701 : reg (bv 256)) (v_2702 : reg (bv 256)) => do
      v_6516 <- getRegister v_2700;
      v_6518 <- getRegister v_2701;
      setRegister (lhs.of_reg v_2702) (concat (concat (extract v_6516 64 96) (extract v_6518 64 96)) (concat (concat (extract v_6516 96 128) (extract v_6518 96 128)) (concat (concat (extract v_6516 192 224) (extract v_6518 192 224)) (concat (extract v_6516 224 256) (extract v_6518 224 256)))));
      pure ()
    pat_end;
    pattern fun (v_2684 : Mem) (v_2685 : reg (bv 128)) (v_2686 : reg (bv 128)) => do
      v_12792 <- evaluateAddress v_2684;
      v_12793 <- load v_12792 16;
      v_12795 <- getRegister v_2685;
      setRegister (lhs.of_reg v_2686) (concat (concat (extract v_12793 64 96) (extract v_12795 64 96)) (concat (extract v_12793 96 128) (extract v_12795 96 128)));
      pure ()
    pat_end;
    pattern fun (v_2695 : Mem) (v_2696 : reg (bv 256)) (v_2697 : reg (bv 256)) => do
      v_12803 <- evaluateAddress v_2695;
      v_12804 <- load v_12803 32;
      v_12806 <- getRegister v_2696;
      setRegister (lhs.of_reg v_2697) (concat (concat (extract v_12804 64 96) (extract v_12806 64 96)) (concat (concat (extract v_12804 96 128) (extract v_12806 96 128)) (concat (concat (extract v_12804 192 224) (extract v_12806 192 224)) (concat (extract v_12804 224 256) (extract v_12806 224 256)))));
      pure ()
    pat_end
