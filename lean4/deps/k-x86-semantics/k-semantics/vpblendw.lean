def vpblendw1 : instruction :=
  definst "vpblendw" $ do
    pattern fun (v_2678 : imm int) (v_2673 : reg (bv 128)) (v_2674 : reg (bv 128)) (v_2675 : reg (bv 128)) => do
      v_6843 <- eval (handleImmediateWithSignExtend v_2678 8 8);
      v_6846 <- getRegister v_2674;
      v_6848 <- getRegister v_2673;
      setRegister (lhs.of_reg v_2675) (concat (mux (eq (extract v_6843 0 1) (expression.bv_nat 1 0)) (extract v_6846 0 16) (extract v_6848 0 16)) (concat (mux (eq (extract v_6843 1 2) (expression.bv_nat 1 0)) (extract v_6846 16 32) (extract v_6848 16 32)) (concat (mux (eq (extract v_6843 2 3) (expression.bv_nat 1 0)) (extract v_6846 32 48) (extract v_6848 32 48)) (concat (mux (eq (extract v_6843 3 4) (expression.bv_nat 1 0)) (extract v_6846 48 64) (extract v_6848 48 64)) (concat (mux (eq (extract v_6843 4 5) (expression.bv_nat 1 0)) (extract v_6846 64 80) (extract v_6848 64 80)) (concat (mux (eq (extract v_6843 5 6) (expression.bv_nat 1 0)) (extract v_6846 80 96) (extract v_6848 80 96)) (concat (mux (eq (extract v_6843 6 7) (expression.bv_nat 1 0)) (extract v_6846 96 112) (extract v_6848 96 112)) (mux (eq (extract v_6843 7 8) (expression.bv_nat 1 0)) (extract v_6846 112 128) (extract v_6848 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2688 : imm int) (v_2690 : reg (bv 256)) (v_2691 : reg (bv 256)) (v_2692 : reg (bv 256)) => do
      v_6900 <- eval (handleImmediateWithSignExtend v_2688 8 8);
      v_6902 <- eval (eq (extract v_6900 0 1) (expression.bv_nat 1 0));
      v_6903 <- getRegister v_2691;
      v_6905 <- getRegister v_2690;
      v_6909 <- eval (eq (extract v_6900 1 2) (expression.bv_nat 1 0));
      v_6914 <- eval (eq (extract v_6900 2 3) (expression.bv_nat 1 0));
      v_6919 <- eval (eq (extract v_6900 3 4) (expression.bv_nat 1 0));
      v_6924 <- eval (eq (extract v_6900 4 5) (expression.bv_nat 1 0));
      v_6929 <- eval (eq (extract v_6900 5 6) (expression.bv_nat 1 0));
      v_6934 <- eval (eq (extract v_6900 6 7) (expression.bv_nat 1 0));
      v_6939 <- eval (eq (extract v_6900 7 8) (expression.bv_nat 1 0));
      setRegister (lhs.of_reg v_2692) (concat (mux v_6902 (extract v_6903 0 16) (extract v_6905 0 16)) (concat (mux v_6909 (extract v_6903 16 32) (extract v_6905 16 32)) (concat (mux v_6914 (extract v_6903 32 48) (extract v_6905 32 48)) (concat (mux v_6919 (extract v_6903 48 64) (extract v_6905 48 64)) (concat (mux v_6924 (extract v_6903 64 80) (extract v_6905 64 80)) (concat (mux v_6929 (extract v_6903 80 96) (extract v_6905 80 96)) (concat (mux v_6934 (extract v_6903 96 112) (extract v_6905 96 112)) (concat (mux v_6939 (extract v_6903 112 128) (extract v_6905 112 128)) (concat (mux v_6902 (extract v_6903 128 144) (extract v_6905 128 144)) (concat (mux v_6909 (extract v_6903 144 160) (extract v_6905 144 160)) (concat (mux v_6914 (extract v_6903 160 176) (extract v_6905 160 176)) (concat (mux v_6919 (extract v_6903 176 192) (extract v_6905 176 192)) (concat (mux v_6924 (extract v_6903 192 208) (extract v_6905 192 208)) (concat (mux v_6929 (extract v_6903 208 224) (extract v_6905 208 224)) (concat (mux v_6934 (extract v_6903 224 240) (extract v_6905 224 240)) (mux v_6939 (extract v_6903 240 256) (extract v_6905 240 256)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2672 : imm int) (v_2671 : Mem) (v_2667 : reg (bv 128)) (v_2668 : reg (bv 128)) => do
      v_15748 <- eval (handleImmediateWithSignExtend v_2672 8 8);
      v_15751 <- getRegister v_2667;
      v_15753 <- evaluateAddress v_2671;
      v_15754 <- load v_15753 16;
      setRegister (lhs.of_reg v_2668) (concat (mux (eq (extract v_15748 0 1) (expression.bv_nat 1 0)) (extract v_15751 0 16) (extract v_15754 0 16)) (concat (mux (eq (extract v_15748 1 2) (expression.bv_nat 1 0)) (extract v_15751 16 32) (extract v_15754 16 32)) (concat (mux (eq (extract v_15748 2 3) (expression.bv_nat 1 0)) (extract v_15751 32 48) (extract v_15754 32 48)) (concat (mux (eq (extract v_15748 3 4) (expression.bv_nat 1 0)) (extract v_15751 48 64) (extract v_15754 48 64)) (concat (mux (eq (extract v_15748 4 5) (expression.bv_nat 1 0)) (extract v_15751 64 80) (extract v_15754 64 80)) (concat (mux (eq (extract v_15748 5 6) (expression.bv_nat 1 0)) (extract v_15751 80 96) (extract v_15754 80 96)) (concat (mux (eq (extract v_15748 6 7) (expression.bv_nat 1 0)) (extract v_15751 96 112) (extract v_15754 96 112)) (mux (eq (extract v_15748 7 8) (expression.bv_nat 1 0)) (extract v_15751 112 128) (extract v_15754 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_2683 : imm int) (v_2682 : Mem) (v_2684 : reg (bv 256)) (v_2685 : reg (bv 256)) => do
      v_15800 <- eval (handleImmediateWithSignExtend v_2683 8 8);
      v_15802 <- eval (eq (extract v_15800 0 1) (expression.bv_nat 1 0));
      v_15803 <- getRegister v_2684;
      v_15805 <- evaluateAddress v_2682;
      v_15806 <- load v_15805 32;
      v_15810 <- eval (eq (extract v_15800 1 2) (expression.bv_nat 1 0));
      v_15815 <- eval (eq (extract v_15800 2 3) (expression.bv_nat 1 0));
      v_15820 <- eval (eq (extract v_15800 3 4) (expression.bv_nat 1 0));
      v_15825 <- eval (eq (extract v_15800 4 5) (expression.bv_nat 1 0));
      v_15830 <- eval (eq (extract v_15800 5 6) (expression.bv_nat 1 0));
      v_15835 <- eval (eq (extract v_15800 6 7) (expression.bv_nat 1 0));
      v_15840 <- eval (eq (extract v_15800 7 8) (expression.bv_nat 1 0));
      setRegister (lhs.of_reg v_2685) (concat (mux v_15802 (extract v_15803 0 16) (extract v_15806 0 16)) (concat (mux v_15810 (extract v_15803 16 32) (extract v_15806 16 32)) (concat (mux v_15815 (extract v_15803 32 48) (extract v_15806 32 48)) (concat (mux v_15820 (extract v_15803 48 64) (extract v_15806 48 64)) (concat (mux v_15825 (extract v_15803 64 80) (extract v_15806 64 80)) (concat (mux v_15830 (extract v_15803 80 96) (extract v_15806 80 96)) (concat (mux v_15835 (extract v_15803 96 112) (extract v_15806 96 112)) (concat (mux v_15840 (extract v_15803 112 128) (extract v_15806 112 128)) (concat (mux v_15802 (extract v_15803 128 144) (extract v_15806 128 144)) (concat (mux v_15810 (extract v_15803 144 160) (extract v_15806 144 160)) (concat (mux v_15815 (extract v_15803 160 176) (extract v_15806 160 176)) (concat (mux v_15820 (extract v_15803 176 192) (extract v_15806 176 192)) (concat (mux v_15825 (extract v_15803 192 208) (extract v_15806 192 208)) (concat (mux v_15830 (extract v_15803 208 224) (extract v_15806 208 224)) (concat (mux v_15835 (extract v_15803 224 240) (extract v_15806 224 240)) (mux v_15840 (extract v_15803 240 256) (extract v_15806 240 256)))))))))))))))));
      pure ()
    pat_end
