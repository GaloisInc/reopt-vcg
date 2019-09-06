def vbroadcastss1 : instruction :=
  definst "vbroadcastss" $ do
    pattern fun (v_2979 : reg (bv 128)) (v_2980 : reg (bv 128)) => do
      v_5497 <- getRegister v_2979;
      v_5498 <- eval (extract v_5497 96 128);
      setRegister (lhs.of_reg v_2980) (concat (concat (concat v_5498 v_5498) v_5498) v_5498);
      pure ()
    pat_end;
    pattern fun (v_2989 : reg (bv 128)) (v_2985 : reg (bv 256)) => do
      v_5507 <- getRegister v_2989;
      v_5508 <- eval (extract v_5507 96 128);
      setRegister (lhs.of_reg v_2985) (concat (concat (concat (concat (concat (concat (concat v_5508 v_5508) v_5508) v_5508) v_5508) v_5508) v_5508) v_5508);
      pure ()
    pat_end;
    pattern fun (v_2972 : Mem) (v_2975 : reg (bv 128)) => do
      v_9689 <- evaluateAddress v_2972;
      v_9690 <- load v_9689 4;
      setRegister (lhs.of_reg v_2975) (concat (concat (concat v_9690 v_9690) v_9690) v_9690);
      pure ()
    pat_end;
    pattern fun (v_2981 : Mem) (v_2982 : reg (bv 256)) => do
      v_9695 <- evaluateAddress v_2981;
      v_9696 <- load v_9695 4;
      setRegister (lhs.of_reg v_2982) (concat (concat (concat (concat (concat (concat (concat v_9696 v_9696) v_9696) v_9696) v_9696) v_9696) v_9696) v_9696);
      pure ()
    pat_end
