def vpbroadcastq1 : instruction :=
  definst "vpbroadcastq" $ do
    pattern fun (v_2813 : reg (bv 128)) (v_2814 : reg (bv 128)) => do
      v_6996 <- getRegister v_2813;
      setRegister (lhs.of_reg v_2814) (concat (extract v_6996 64 128) (extract v_6996 64 128));
      pure ()
    pat_end;
    pattern fun (v_2823 : reg (bv 128)) (v_2822 : reg (bv 256)) => do
      v_7004 <- getRegister v_2823;
      setRegister (lhs.of_reg v_2822) (concat (concat (extract v_7004 64 128) (extract v_7004 64 128)) (concat (extract v_7004 64 128) (extract v_7004 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2809 : Mem) (v_2810 : reg (bv 128)) => do
      v_15629 <- evaluateAddress v_2809;
      v_15630 <- load v_15629 8;
      setRegister (lhs.of_reg v_2810) (concat v_15630 v_15630);
      pure ()
    pat_end;
    pattern fun (v_2818 : Mem) (v_2819 : reg (bv 256)) => do
      v_15633 <- evaluateAddress v_2818;
      v_15634 <- load v_15633 8;
      setRegister (lhs.of_reg v_2819) (concat (concat v_15634 v_15634) (concat v_15634 v_15634));
      pure ()
    pat_end
