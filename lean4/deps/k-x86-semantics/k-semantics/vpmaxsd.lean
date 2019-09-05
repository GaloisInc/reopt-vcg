def vpmaxsd1 : instruction :=
  definst "vpmaxsd" $ do
    pattern fun (v_3513 : reg (bv 128)) (v_3514 : reg (bv 128)) (v_3515 : reg (bv 128)) => do
      v_10613 <- getRegister v_3514;
      v_10614 <- eval (extract v_10613 0 32);
      v_10615 <- getRegister v_3513;
      v_10616 <- eval (extract v_10615 0 32);
      v_10619 <- eval (extract v_10613 32 64);
      v_10620 <- eval (extract v_10615 32 64);
      v_10623 <- eval (extract v_10613 64 96);
      v_10624 <- eval (extract v_10615 64 96);
      v_10627 <- eval (extract v_10613 96 128);
      v_10628 <- eval (extract v_10615 96 128);
      setRegister (lhs.of_reg v_3515) (concat (mux (sgt v_10614 v_10616) v_10614 v_10616) (concat (mux (sgt v_10619 v_10620) v_10619 v_10620) (concat (mux (sgt v_10623 v_10624) v_10623 v_10624) (mux (sgt v_10627 v_10628) v_10627 v_10628))));
      pure ()
    pat_end;
    pattern fun (v_3523 : reg (bv 256)) (v_3524 : reg (bv 256)) (v_3525 : reg (bv 256)) => do
      v_10640 <- getRegister v_3524;
      v_10641 <- eval (extract v_10640 0 32);
      v_10642 <- getRegister v_3523;
      v_10643 <- eval (extract v_10642 0 32);
      v_10646 <- eval (extract v_10640 32 64);
      v_10647 <- eval (extract v_10642 32 64);
      v_10650 <- eval (extract v_10640 64 96);
      v_10651 <- eval (extract v_10642 64 96);
      v_10654 <- eval (extract v_10640 96 128);
      v_10655 <- eval (extract v_10642 96 128);
      v_10658 <- eval (extract v_10640 128 160);
      v_10659 <- eval (extract v_10642 128 160);
      v_10662 <- eval (extract v_10640 160 192);
      v_10663 <- eval (extract v_10642 160 192);
      v_10666 <- eval (extract v_10640 192 224);
      v_10667 <- eval (extract v_10642 192 224);
      v_10670 <- eval (extract v_10640 224 256);
      v_10671 <- eval (extract v_10642 224 256);
      setRegister (lhs.of_reg v_3525) (concat (mux (sgt v_10641 v_10643) v_10641 v_10643) (concat (mux (sgt v_10646 v_10647) v_10646 v_10647) (concat (mux (sgt v_10650 v_10651) v_10650 v_10651) (concat (mux (sgt v_10654 v_10655) v_10654 v_10655) (concat (mux (sgt v_10658 v_10659) v_10658 v_10659) (concat (mux (sgt v_10662 v_10663) v_10662 v_10663) (concat (mux (sgt v_10666 v_10667) v_10666 v_10667) (mux (sgt v_10670 v_10671) v_10670 v_10671))))))));
      pure ()
    pat_end;
    pattern fun (v_3507 : Mem) (v_3508 : reg (bv 128)) (v_3509 : reg (bv 128)) => do
      v_18986 <- getRegister v_3508;
      v_18987 <- eval (extract v_18986 0 32);
      v_18988 <- evaluateAddress v_3507;
      v_18989 <- load v_18988 16;
      v_18990 <- eval (extract v_18989 0 32);
      v_18993 <- eval (extract v_18986 32 64);
      v_18994 <- eval (extract v_18989 32 64);
      v_18997 <- eval (extract v_18986 64 96);
      v_18998 <- eval (extract v_18989 64 96);
      v_19001 <- eval (extract v_18986 96 128);
      v_19002 <- eval (extract v_18989 96 128);
      setRegister (lhs.of_reg v_3509) (concat (mux (sgt v_18987 v_18990) v_18987 v_18990) (concat (mux (sgt v_18993 v_18994) v_18993 v_18994) (concat (mux (sgt v_18997 v_18998) v_18997 v_18998) (mux (sgt v_19001 v_19002) v_19001 v_19002))));
      pure ()
    pat_end;
    pattern fun (v_3518 : Mem) (v_3519 : reg (bv 256)) (v_3520 : reg (bv 256)) => do
      v_19009 <- getRegister v_3519;
      v_19010 <- eval (extract v_19009 0 32);
      v_19011 <- evaluateAddress v_3518;
      v_19012 <- load v_19011 32;
      v_19013 <- eval (extract v_19012 0 32);
      v_19016 <- eval (extract v_19009 32 64);
      v_19017 <- eval (extract v_19012 32 64);
      v_19020 <- eval (extract v_19009 64 96);
      v_19021 <- eval (extract v_19012 64 96);
      v_19024 <- eval (extract v_19009 96 128);
      v_19025 <- eval (extract v_19012 96 128);
      v_19028 <- eval (extract v_19009 128 160);
      v_19029 <- eval (extract v_19012 128 160);
      v_19032 <- eval (extract v_19009 160 192);
      v_19033 <- eval (extract v_19012 160 192);
      v_19036 <- eval (extract v_19009 192 224);
      v_19037 <- eval (extract v_19012 192 224);
      v_19040 <- eval (extract v_19009 224 256);
      v_19041 <- eval (extract v_19012 224 256);
      setRegister (lhs.of_reg v_3520) (concat (mux (sgt v_19010 v_19013) v_19010 v_19013) (concat (mux (sgt v_19016 v_19017) v_19016 v_19017) (concat (mux (sgt v_19020 v_19021) v_19020 v_19021) (concat (mux (sgt v_19024 v_19025) v_19024 v_19025) (concat (mux (sgt v_19028 v_19029) v_19028 v_19029) (concat (mux (sgt v_19032 v_19033) v_19032 v_19033) (concat (mux (sgt v_19036 v_19037) v_19036 v_19037) (mux (sgt v_19040 v_19041) v_19040 v_19041))))))));
      pure ()
    pat_end
