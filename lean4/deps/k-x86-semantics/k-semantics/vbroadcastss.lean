def vbroadcastss1 : instruction :=
  definst "vbroadcastss" $ do
    pattern fun (v_2952 : reg (bv 128)) (v_2953 : reg (bv 128)) => do
      v_5470 <- getRegister v_2952;
      v_5471 <- eval (extract v_5470 96 128);
      setRegister (lhs.of_reg v_2953) (concat (concat (concat v_5471 v_5471) v_5471) v_5471);
      pure ()
    pat_end;
    pattern fun (v_2962 : reg (bv 128)) (v_2960 : reg (bv 256)) => do
      v_5480 <- getRegister v_2962;
      v_5481 <- eval (extract v_5480 96 128);
      setRegister (lhs.of_reg v_2960) (concat (concat (concat (concat (concat (concat (concat v_5481 v_5481) v_5481) v_5481) v_5481) v_5481) v_5481) v_5481);
      pure ()
    pat_end;
    pattern fun (v_2947 : Mem) (v_2948 : reg (bv 128)) => do
      v_9662 <- evaluateAddress v_2947;
      v_9663 <- load v_9662 4;
      setRegister (lhs.of_reg v_2948) (concat (concat (concat v_9663 v_9663) v_9663) v_9663);
      pure ()
    pat_end;
    pattern fun (v_2956 : Mem) (v_2957 : reg (bv 256)) => do
      v_9668 <- evaluateAddress v_2956;
      v_9669 <- load v_9668 4;
      setRegister (lhs.of_reg v_2957) (concat (concat (concat (concat (concat (concat (concat v_9669 v_9669) v_9669) v_9669) v_9669) v_9669) v_9669) v_9669);
      pure ()
    pat_end
