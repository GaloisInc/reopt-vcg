def vpmaxsd1 : instruction :=
  definst "vpmaxsd" $ do
    pattern fun (v_3539 : reg (bv 128)) (v_3540 : reg (bv 128)) (v_3541 : reg (bv 128)) => do
      v_10640 <- getRegister v_3540;
      v_10641 <- eval (extract v_10640 0 32);
      v_10642 <- getRegister v_3539;
      v_10643 <- eval (extract v_10642 0 32);
      v_10646 <- eval (extract v_10640 32 64);
      v_10647 <- eval (extract v_10642 32 64);
      v_10650 <- eval (extract v_10640 64 96);
      v_10651 <- eval (extract v_10642 64 96);
      v_10654 <- eval (extract v_10640 96 128);
      v_10655 <- eval (extract v_10642 96 128);
      setRegister (lhs.of_reg v_3541) (concat (mux (sgt v_10641 v_10643) v_10641 v_10643) (concat (mux (sgt v_10646 v_10647) v_10646 v_10647) (concat (mux (sgt v_10650 v_10651) v_10650 v_10651) (mux (sgt v_10654 v_10655) v_10654 v_10655))));
      pure ()
    pat_end;
    pattern fun (v_3550 : reg (bv 256)) (v_3551 : reg (bv 256)) (v_3552 : reg (bv 256)) => do
      v_10667 <- getRegister v_3551;
      v_10668 <- eval (extract v_10667 0 32);
      v_10669 <- getRegister v_3550;
      v_10670 <- eval (extract v_10669 0 32);
      v_10673 <- eval (extract v_10667 32 64);
      v_10674 <- eval (extract v_10669 32 64);
      v_10677 <- eval (extract v_10667 64 96);
      v_10678 <- eval (extract v_10669 64 96);
      v_10681 <- eval (extract v_10667 96 128);
      v_10682 <- eval (extract v_10669 96 128);
      v_10685 <- eval (extract v_10667 128 160);
      v_10686 <- eval (extract v_10669 128 160);
      v_10689 <- eval (extract v_10667 160 192);
      v_10690 <- eval (extract v_10669 160 192);
      v_10693 <- eval (extract v_10667 192 224);
      v_10694 <- eval (extract v_10669 192 224);
      v_10697 <- eval (extract v_10667 224 256);
      v_10698 <- eval (extract v_10669 224 256);
      setRegister (lhs.of_reg v_3552) (concat (mux (sgt v_10668 v_10670) v_10668 v_10670) (concat (mux (sgt v_10673 v_10674) v_10673 v_10674) (concat (mux (sgt v_10677 v_10678) v_10677 v_10678) (concat (mux (sgt v_10681 v_10682) v_10681 v_10682) (concat (mux (sgt v_10685 v_10686) v_10685 v_10686) (concat (mux (sgt v_10689 v_10690) v_10689 v_10690) (concat (mux (sgt v_10693 v_10694) v_10693 v_10694) (mux (sgt v_10697 v_10698) v_10697 v_10698))))))));
      pure ()
    pat_end;
    pattern fun (v_3534 : Mem) (v_3535 : reg (bv 128)) (v_3536 : reg (bv 128)) => do
      v_19013 <- getRegister v_3535;
      v_19014 <- eval (extract v_19013 0 32);
      v_19015 <- evaluateAddress v_3534;
      v_19016 <- load v_19015 16;
      v_19017 <- eval (extract v_19016 0 32);
      v_19020 <- eval (extract v_19013 32 64);
      v_19021 <- eval (extract v_19016 32 64);
      v_19024 <- eval (extract v_19013 64 96);
      v_19025 <- eval (extract v_19016 64 96);
      v_19028 <- eval (extract v_19013 96 128);
      v_19029 <- eval (extract v_19016 96 128);
      setRegister (lhs.of_reg v_3536) (concat (mux (sgt v_19014 v_19017) v_19014 v_19017) (concat (mux (sgt v_19020 v_19021) v_19020 v_19021) (concat (mux (sgt v_19024 v_19025) v_19024 v_19025) (mux (sgt v_19028 v_19029) v_19028 v_19029))));
      pure ()
    pat_end;
    pattern fun (v_3545 : Mem) (v_3546 : reg (bv 256)) (v_3547 : reg (bv 256)) => do
      v_19036 <- getRegister v_3546;
      v_19037 <- eval (extract v_19036 0 32);
      v_19038 <- evaluateAddress v_3545;
      v_19039 <- load v_19038 32;
      v_19040 <- eval (extract v_19039 0 32);
      v_19043 <- eval (extract v_19036 32 64);
      v_19044 <- eval (extract v_19039 32 64);
      v_19047 <- eval (extract v_19036 64 96);
      v_19048 <- eval (extract v_19039 64 96);
      v_19051 <- eval (extract v_19036 96 128);
      v_19052 <- eval (extract v_19039 96 128);
      v_19055 <- eval (extract v_19036 128 160);
      v_19056 <- eval (extract v_19039 128 160);
      v_19059 <- eval (extract v_19036 160 192);
      v_19060 <- eval (extract v_19039 160 192);
      v_19063 <- eval (extract v_19036 192 224);
      v_19064 <- eval (extract v_19039 192 224);
      v_19067 <- eval (extract v_19036 224 256);
      v_19068 <- eval (extract v_19039 224 256);
      setRegister (lhs.of_reg v_3547) (concat (mux (sgt v_19037 v_19040) v_19037 v_19040) (concat (mux (sgt v_19043 v_19044) v_19043 v_19044) (concat (mux (sgt v_19047 v_19048) v_19047 v_19048) (concat (mux (sgt v_19051 v_19052) v_19051 v_19052) (concat (mux (sgt v_19055 v_19056) v_19055 v_19056) (concat (mux (sgt v_19059 v_19060) v_19059 v_19060) (concat (mux (sgt v_19063 v_19064) v_19063 v_19064) (mux (sgt v_19067 v_19068) v_19067 v_19068))))))));
      pure ()
    pat_end
