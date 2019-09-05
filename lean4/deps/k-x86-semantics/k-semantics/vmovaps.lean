def vmovaps1 : instruction :=
  definst "vmovaps" $ do
    pattern fun (v_2763 : Mem) (v_2764 : reg (bv 128)) => do
      v_10134 <- evaluateAddress v_2763;
      v_10135 <- load v_10134 16;
      setRegister (lhs.of_reg v_2764) v_10135;
      pure ()
    pat_end;
    pattern fun (v_2772 : Mem) (v_2773 : reg (bv 256)) => do
      v_10137 <- evaluateAddress v_2772;
      v_10138 <- load v_10137 32;
      setRegister (lhs.of_reg v_2773) v_10138;
      pure ()
    pat_end;
    pattern fun (v_2756 : reg (bv 128)) (v_2755 : Mem) => do
      v_12408 <- evaluateAddress v_2755;
      v_12409 <- getRegister v_2756;
      store v_12408 v_12409 16;
      pure ()
    pat_end;
    pattern fun (v_2760 : reg (bv 256)) (v_2759 : Mem) => do
      v_12411 <- evaluateAddress v_2759;
      v_12412 <- getRegister v_2760;
      store v_12411 v_12412 32;
      pure ()
    pat_end
