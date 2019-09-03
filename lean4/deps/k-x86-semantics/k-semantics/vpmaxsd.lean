def vpmaxsd1 : instruction :=
  definst "vpmaxsd" $ do
    pattern fun (v_3459 : reg (bv 128)) (v_3460 : reg (bv 128)) (v_3461 : reg (bv 128)) => do
      v_10810 <- getRegister v_3460;
      v_10811 <- eval (extract v_10810 0 32);
      v_10812 <- getRegister v_3459;
      v_10813 <- eval (extract v_10812 0 32);
      v_10816 <- eval (extract v_10810 32 64);
      v_10817 <- eval (extract v_10812 32 64);
      v_10820 <- eval (extract v_10810 64 96);
      v_10821 <- eval (extract v_10812 64 96);
      v_10824 <- eval (extract v_10810 96 128);
      v_10825 <- eval (extract v_10812 96 128);
      setRegister (lhs.of_reg v_3461) (concat (mux (sgt v_10811 v_10813) v_10811 v_10813) (concat (mux (sgt v_10816 v_10817) v_10816 v_10817) (concat (mux (sgt v_10820 v_10821) v_10820 v_10821) (mux (sgt v_10824 v_10825) v_10824 v_10825))));
      pure ()
    pat_end;
    pattern fun (v_3473 : reg (bv 256)) (v_3474 : reg (bv 256)) (v_3475 : reg (bv 256)) => do
      v_10837 <- getRegister v_3474;
      v_10838 <- eval (extract v_10837 0 32);
      v_10839 <- getRegister v_3473;
      v_10840 <- eval (extract v_10839 0 32);
      v_10843 <- eval (extract v_10837 32 64);
      v_10844 <- eval (extract v_10839 32 64);
      v_10847 <- eval (extract v_10837 64 96);
      v_10848 <- eval (extract v_10839 64 96);
      v_10851 <- eval (extract v_10837 96 128);
      v_10852 <- eval (extract v_10839 96 128);
      v_10855 <- eval (extract v_10837 128 160);
      v_10856 <- eval (extract v_10839 128 160);
      v_10859 <- eval (extract v_10837 160 192);
      v_10860 <- eval (extract v_10839 160 192);
      v_10863 <- eval (extract v_10837 192 224);
      v_10864 <- eval (extract v_10839 192 224);
      v_10867 <- eval (extract v_10837 224 256);
      v_10868 <- eval (extract v_10839 224 256);
      setRegister (lhs.of_reg v_3475) (concat (mux (sgt v_10838 v_10840) v_10838 v_10840) (concat (mux (sgt v_10843 v_10844) v_10843 v_10844) (concat (mux (sgt v_10847 v_10848) v_10847 v_10848) (concat (mux (sgt v_10851 v_10852) v_10851 v_10852) (concat (mux (sgt v_10855 v_10856) v_10855 v_10856) (concat (mux (sgt v_10859 v_10860) v_10859 v_10860) (concat (mux (sgt v_10863 v_10864) v_10863 v_10864) (mux (sgt v_10867 v_10868) v_10867 v_10868))))))));
      pure ()
    pat_end;
    pattern fun (v_3458 : Mem) (v_3454 : reg (bv 128)) (v_3455 : reg (bv 128)) => do
      v_19443 <- getRegister v_3454;
      v_19444 <- eval (extract v_19443 0 32);
      v_19445 <- evaluateAddress v_3458;
      v_19446 <- load v_19445 16;
      v_19447 <- eval (extract v_19446 0 32);
      v_19450 <- eval (extract v_19443 32 64);
      v_19451 <- eval (extract v_19446 32 64);
      v_19454 <- eval (extract v_19443 64 96);
      v_19455 <- eval (extract v_19446 64 96);
      v_19458 <- eval (extract v_19443 96 128);
      v_19459 <- eval (extract v_19446 96 128);
      setRegister (lhs.of_reg v_3455) (concat (mux (sgt v_19444 v_19447) v_19444 v_19447) (concat (mux (sgt v_19450 v_19451) v_19450 v_19451) (concat (mux (sgt v_19454 v_19455) v_19454 v_19455) (mux (sgt v_19458 v_19459) v_19458 v_19459))));
      pure ()
    pat_end;
    pattern fun (v_3467 : Mem) (v_3468 : reg (bv 256)) (v_3469 : reg (bv 256)) => do
      v_19466 <- getRegister v_3468;
      v_19467 <- eval (extract v_19466 0 32);
      v_19468 <- evaluateAddress v_3467;
      v_19469 <- load v_19468 32;
      v_19470 <- eval (extract v_19469 0 32);
      v_19473 <- eval (extract v_19466 32 64);
      v_19474 <- eval (extract v_19469 32 64);
      v_19477 <- eval (extract v_19466 64 96);
      v_19478 <- eval (extract v_19469 64 96);
      v_19481 <- eval (extract v_19466 96 128);
      v_19482 <- eval (extract v_19469 96 128);
      v_19485 <- eval (extract v_19466 128 160);
      v_19486 <- eval (extract v_19469 128 160);
      v_19489 <- eval (extract v_19466 160 192);
      v_19490 <- eval (extract v_19469 160 192);
      v_19493 <- eval (extract v_19466 192 224);
      v_19494 <- eval (extract v_19469 192 224);
      v_19497 <- eval (extract v_19466 224 256);
      v_19498 <- eval (extract v_19469 224 256);
      setRegister (lhs.of_reg v_3469) (concat (mux (sgt v_19467 v_19470) v_19467 v_19470) (concat (mux (sgt v_19473 v_19474) v_19473 v_19474) (concat (mux (sgt v_19477 v_19478) v_19477 v_19478) (concat (mux (sgt v_19481 v_19482) v_19481 v_19482) (concat (mux (sgt v_19485 v_19486) v_19485 v_19486) (concat (mux (sgt v_19489 v_19490) v_19489 v_19490) (concat (mux (sgt v_19493 v_19494) v_19493 v_19494) (mux (sgt v_19497 v_19498) v_19497 v_19498))))))));
      pure ()
    pat_end
