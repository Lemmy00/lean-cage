import LeanCageHost.Bytes

namespace LeanCage.Host.PrivateNames

def prefixText : String := ".leancage-private-"
def attributeName : ByteArray := "user.leancage.private".toUTF8
def attributeValue : ByteArray := ByteArray.mk #[1]
def reserved (name : String) : Bool := name.startsWith prefixText
def reservedBytes (name : ByteArray) : Bool :=
  prefixText.toUTF8.data.toList.isPrefixOf name.data.toList
def areaName (uid : Nat) : ByteArray := (prefixText ++ toString uid).toUTF8

end LeanCage.Host.PrivateNames
