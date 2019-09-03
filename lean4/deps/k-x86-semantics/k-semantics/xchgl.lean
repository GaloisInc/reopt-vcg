def xchgl1 : instruction :=
  definst "xchgl" $ do
    pattern fun (v_2656 : reg (bv 32)) eax => do
      v_4316 <- getRegister v_2656;
      v_4317 <- getRegister rax;
      setRegister (lhs.of_reg v_2656) (extract v_4317 32 64);
      setRegister eax v_4316;
      pure ()
    pat_end;
    pattern fun eax (v_2664 : reg (bv 32)) => do
      v_4325 <- getRegister v_2664;
      v_4326 <- getRegister rax;
      setRegister (lhs.of_reg v_2664) (extract v_4326 32 64);
      setRegister eax v_4325;
      pure ()
    pat_end;
    pattern fun (v_2672 : reg (bv 32)) (v_2673 : reg (bv 32)) => do
      v_4334 <- getRegister v_2672;
      v_4335 <- getRegister v_2673;
      setRegister (lhs.of_reg v_2672) v_4335;
      setRegister (lhs.of_reg v_2673) v_4334;
      pure ()
    pat_end;
    pattern fun (v_2660 : reg (bv 32)) (v_2661 : Mem) => do
      v_7583 <- evaluateAddress v_2661;
      v_7584 <- getRegister v_2660;
      store v_7583 v_7584 4;
      setRegister (lhs.of_reg v_2660) v_7586;
      pure ()
    pat_end;
    pattern fun (v_2669 : Mem) (v_2668 : reg (bv 32)) => do
      v_7588 <- evaluateAddress v_2669;
      v_7589 <- getRegister v_2668;
      store v_7588 v_7589 4;
      setRegister (lhs.of_reg v_2668) v_7591;
      pure ()
    pat_end
