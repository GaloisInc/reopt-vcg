def vpackusdw1 : instruction :=
  definst "vpackusdw" $ do
    pattern fun (v_3278 : reg (bv 128)) (v_3279 : reg (bv 128)) (v_3280 : reg (bv 128)) => do
      v_6552 <- getRegister v_3278;
      v_6553 <- eval (extract v_6552 0 32);
      v_6559 <- eval (extract v_6552 32 64);
      v_6565 <- eval (extract v_6552 64 96);
      v_6571 <- eval (extract v_6552 96 128);
      v_6577 <- getRegister v_3279;
      v_6578 <- eval (extract v_6577 0 32);
      v_6584 <- eval (extract v_6577 32 64);
      v_6590 <- eval (extract v_6577 64 96);
      v_6596 <- eval (extract v_6577 96 128);
      setRegister (lhs.of_reg v_3280) (concat (mux (sgt v_6553 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6553 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6552 16 32))) (concat (mux (sgt v_6559 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6559 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6552 48 64))) (concat (mux (sgt v_6565 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6565 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6552 80 96))) (concat (mux (sgt v_6571 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6571 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6552 112 128))) (concat (mux (sgt v_6578 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6578 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6577 16 32))) (concat (mux (sgt v_6584 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6584 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6577 48 64))) (concat (mux (sgt v_6590 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6590 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6577 80 96))) (mux (sgt v_6596 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6596 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6577 112 128))))))))));
      pure ()
    pat_end;
    pattern fun (v_3289 : reg (bv 256)) (v_3290 : reg (bv 256)) (v_3291 : reg (bv 256)) => do
      v_6615 <- getRegister v_3289;
      v_6616 <- eval (extract v_6615 0 32);
      v_6622 <- eval (extract v_6615 32 64);
      v_6628 <- eval (extract v_6615 64 96);
      v_6634 <- eval (extract v_6615 96 128);
      v_6640 <- getRegister v_3290;
      v_6641 <- eval (extract v_6640 0 32);
      v_6647 <- eval (extract v_6640 32 64);
      v_6653 <- eval (extract v_6640 64 96);
      v_6659 <- eval (extract v_6640 96 128);
      v_6665 <- eval (extract v_6615 128 160);
      v_6671 <- eval (extract v_6615 160 192);
      v_6677 <- eval (extract v_6615 192 224);
      v_6683 <- eval (extract v_6615 224 256);
      v_6689 <- eval (extract v_6640 128 160);
      v_6695 <- eval (extract v_6640 160 192);
      v_6701 <- eval (extract v_6640 192 224);
      v_6707 <- eval (extract v_6640 224 256);
      setRegister (lhs.of_reg v_3291) (concat (mux (sgt v_6616 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6616 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6615 16 32))) (concat (mux (sgt v_6622 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6622 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6615 48 64))) (concat (mux (sgt v_6628 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6628 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6615 80 96))) (concat (mux (sgt v_6634 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6634 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6615 112 128))) (concat (mux (sgt v_6641 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6641 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6640 16 32))) (concat (mux (sgt v_6647 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6647 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6640 48 64))) (concat (mux (sgt v_6653 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6653 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6640 80 96))) (concat (mux (sgt v_6659 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6659 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6640 112 128))) (concat (mux (sgt v_6665 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6665 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6615 144 160))) (concat (mux (sgt v_6671 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6671 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6615 176 192))) (concat (mux (sgt v_6677 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6677 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6615 208 224))) (concat (mux (sgt v_6683 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6683 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6615 240 256))) (concat (mux (sgt v_6689 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6689 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6640 144 160))) (concat (mux (sgt v_6695 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6695 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6640 176 192))) (concat (mux (sgt v_6701 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6701 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6640 208 224))) (mux (sgt v_6707 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6707 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6640 240 256))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3272 : Mem) (v_3273 : reg (bv 128)) (v_3274 : reg (bv 128)) => do
      v_11800 <- evaluateAddress v_3272;
      v_11801 <- load v_11800 16;
      v_11802 <- eval (extract v_11801 0 32);
      v_11808 <- eval (extract v_11801 32 64);
      v_11814 <- eval (extract v_11801 64 96);
      v_11820 <- eval (extract v_11801 96 128);
      v_11826 <- getRegister v_3273;
      v_11827 <- eval (extract v_11826 0 32);
      v_11833 <- eval (extract v_11826 32 64);
      v_11839 <- eval (extract v_11826 64 96);
      v_11845 <- eval (extract v_11826 96 128);
      setRegister (lhs.of_reg v_3274) (concat (mux (sgt v_11802 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11802 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11801 16 32))) (concat (mux (sgt v_11808 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11808 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11801 48 64))) (concat (mux (sgt v_11814 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11814 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11801 80 96))) (concat (mux (sgt v_11820 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11820 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11801 112 128))) (concat (mux (sgt v_11827 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11827 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11826 16 32))) (concat (mux (sgt v_11833 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11833 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11826 48 64))) (concat (mux (sgt v_11839 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11839 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11826 80 96))) (mux (sgt v_11845 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11845 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11826 112 128))))))))));
      pure ()
    pat_end;
    pattern fun (v_3283 : Mem) (v_3284 : reg (bv 256)) (v_3285 : reg (bv 256)) => do
      v_11859 <- evaluateAddress v_3283;
      v_11860 <- load v_11859 32;
      v_11861 <- eval (extract v_11860 0 32);
      v_11867 <- eval (extract v_11860 32 64);
      v_11873 <- eval (extract v_11860 64 96);
      v_11879 <- eval (extract v_11860 96 128);
      v_11885 <- getRegister v_3284;
      v_11886 <- eval (extract v_11885 0 32);
      v_11892 <- eval (extract v_11885 32 64);
      v_11898 <- eval (extract v_11885 64 96);
      v_11904 <- eval (extract v_11885 96 128);
      v_11910 <- eval (extract v_11860 128 160);
      v_11916 <- eval (extract v_11860 160 192);
      v_11922 <- eval (extract v_11860 192 224);
      v_11928 <- eval (extract v_11860 224 256);
      v_11934 <- eval (extract v_11885 128 160);
      v_11940 <- eval (extract v_11885 160 192);
      v_11946 <- eval (extract v_11885 192 224);
      v_11952 <- eval (extract v_11885 224 256);
      setRegister (lhs.of_reg v_3285) (concat (mux (sgt v_11861 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11861 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11860 16 32))) (concat (mux (sgt v_11867 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11867 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11860 48 64))) (concat (mux (sgt v_11873 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11873 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11860 80 96))) (concat (mux (sgt v_11879 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11879 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11860 112 128))) (concat (mux (sgt v_11886 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11886 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11885 16 32))) (concat (mux (sgt v_11892 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11892 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11885 48 64))) (concat (mux (sgt v_11898 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11898 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11885 80 96))) (concat (mux (sgt v_11904 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11904 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11885 112 128))) (concat (mux (sgt v_11910 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11910 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11860 144 160))) (concat (mux (sgt v_11916 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11916 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11860 176 192))) (concat (mux (sgt v_11922 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11922 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11860 208 224))) (concat (mux (sgt v_11928 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11928 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11860 240 256))) (concat (mux (sgt v_11934 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11934 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11885 144 160))) (concat (mux (sgt v_11940 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11940 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11885 176 192))) (concat (mux (sgt v_11946 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11946 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11885 208 224))) (mux (sgt v_11952 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11952 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11885 240 256))))))))))))))))));
      pure ()
    pat_end
