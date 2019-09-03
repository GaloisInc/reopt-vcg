def vpbroadcastb1 : instruction :=
  definst "vpbroadcastb" $ do
    pattern fun (v_2697 : reg (bv 128)) (v_2698 : reg (bv 128)) => do
      v_6987 <- getRegister v_2697;
      v_6988 <- eval (extract v_6987 120 128);
      setRegister (lhs.of_reg v_2698) (concat v_6988 (concat v_6988 (concat v_6988 (concat v_6988 (concat v_6988 (concat v_6988 (concat v_6988 (concat v_6988 (concat v_6988 (concat v_6988 (concat v_6988 (concat v_6988 (concat v_6988 (concat v_6988 (concat v_6988 v_6988)))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2706 : reg (bv 128)) (v_2710 : reg (bv 256)) => do
      v_7009 <- getRegister v_2706;
      v_7010 <- eval (extract v_7009 120 128);
      setRegister (lhs.of_reg v_2710) (concat v_7010 (concat v_7010 (concat v_7010 (concat v_7010 (concat v_7010 (concat v_7010 (concat v_7010 (concat v_7010 (concat v_7010 (concat v_7010 (concat v_7010 (concat v_7010 (concat v_7010 (concat v_7010 (concat v_7010 (concat v_7010 (concat v_7010 (concat v_7010 (concat v_7010 (concat v_7010 (concat v_7010 (concat v_7010 (concat v_7010 (concat v_7010 (concat v_7010 (concat v_7010 (concat v_7010 (concat v_7010 (concat v_7010 (concat v_7010 (concat v_7010 v_7010)))))))))))))))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2696 : Mem) (v_2693 : reg (bv 128)) => do
      v_15884 <- evaluateAddress v_2696;
      v_15885 <- load v_15884 1;
      setRegister (lhs.of_reg v_2693) (concat v_15885 (concat v_15885 (concat v_15885 (concat v_15885 (concat v_15885 (concat v_15885 (concat v_15885 (concat v_15885 (concat v_15885 (concat v_15885 (concat v_15885 (concat v_15885 (concat v_15885 (concat v_15885 (concat v_15885 v_15885)))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2704 : Mem) (v_2705 : reg (bv 256)) => do
      v_15902 <- evaluateAddress v_2704;
      v_15903 <- load v_15902 1;
      setRegister (lhs.of_reg v_2705) (concat v_15903 (concat v_15903 (concat v_15903 (concat v_15903 (concat v_15903 (concat v_15903 (concat v_15903 (concat v_15903 (concat v_15903 (concat v_15903 (concat v_15903 (concat v_15903 (concat v_15903 (concat v_15903 (concat v_15903 (concat v_15903 (concat v_15903 (concat v_15903 (concat v_15903 (concat v_15903 (concat v_15903 (concat v_15903 (concat v_15903 (concat v_15903 (concat v_15903 (concat v_15903 (concat v_15903 (concat v_15903 (concat v_15903 (concat v_15903 (concat v_15903 v_15903)))))))))))))))))))))))))))))));
      pure ()
    pat_end
