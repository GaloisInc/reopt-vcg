def xchgl1 : instruction :=
  definst "xchgl" $ do
    pattern fun (v_2657 : reg (bv 32)) eax => do
      v_4316 <- getRegister v_2657;
      v_4317 <- getRegister rax;
      setRegister (lhs.of_reg v_2657) (extract v_4317 32 64);
      setRegister eax v_4316;
      pure ()
    pat_end;
    pattern fun eax (v_2665 : reg (bv 32)) => do
      v_4325 <- getRegister v_2665;
      v_4326 <- getRegister rax;
      setRegister (lhs.of_reg v_2665) (extract v_4326 32 64);
      setRegister eax v_4325;
      pure ()
    pat_end;
    pattern fun (v_2673 : reg (bv 32)) (v_2674 : reg (bv 32)) => do
      v_4334 <- getRegister v_2674;
      v_4335 <- getRegister v_2673;
      setRegister (lhs.of_reg v_2674) v_4335;
      setRegister (lhs.of_reg v_2673) v_4334;
      pure ()
    pat_end;
    pattern fun (v_2661 : reg (bv 32)) (v_2660 : Mem) => do
      v_7583 <- evaluateAddress v_2660;
      v_7584 <- getRegister v_2661;
      store v_7583 v_7584 4;
      setRegister (lhs.of_reg v_2661) v_7586;
      pure ()
    pat_end;
    pattern fun (v_2668 : Mem) (v_2669 : reg (bv 32)) => do
      v_7588 <- evaluateAddress v_2668;
      v_7589 <- getRegister v_2669;
      store v_7588 v_7589 4;
      setRegister (lhs.of_reg v_2669) v_7591;
      pure ()
    pat_end
