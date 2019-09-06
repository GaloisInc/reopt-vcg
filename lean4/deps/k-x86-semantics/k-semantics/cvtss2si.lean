def cvtss2si1 : instruction :=
  definst "cvtss2si" $ do
    pattern fun (v_2689 : reg (bv 128)) (v_2688 : reg (bv 32)) => do
      v_4300 <- getRegister v_2689;
      setRegister (lhs.of_reg v_2688) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate (extract v_4300 96 128));
      pure ()
    pat_end;
    pattern fun (v_2697 : reg (bv 128)) (v_2698 : reg (bv 64)) => do
      v_4308 <- getRegister v_2697;
      setRegister (lhs.of_reg v_2698) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate (extract v_4308 96 128));
      pure ()
    pat_end;
    pattern fun (v_2684 : Mem) (v_2685 : reg (bv 32)) => do
      v_7978 <- evaluateAddress v_2684;
      v_7979 <- load v_7978 4;
      setRegister (lhs.of_reg v_2685) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int32_truncate v_7979);
      pure ()
    pat_end;
    pattern fun (v_2693 : Mem) (v_2694 : reg (bv 64)) => do
      v_7982 <- evaluateAddress v_2693;
      v_7983 <- load v_7982 4;
      setRegister (lhs.of_reg v_2694) (_(_)_MINT-WRAPPER-SYNTAX cvt_single_to_int64_truncate v_7983);
      pure ()
    pat_end
